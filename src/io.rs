use std::sync::Mutex;
use std::fs::{File, OpenOptions};
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::io::{BufWriter, Write, BufReader, Read, SeekFrom, prelude::*};
use bytes::{Bytes, BytesMut, Buf, BufMut};
use rand::prelude::*;

const PAGE_SIZE: usize = 4096; // size of a page in bytes
const MAX_HEADER_PAGES: usize = PAGE_SIZE / 2; // 2 bytes per header page
const DATA_PAGES_PER_HEADER: usize = PAGE_SIZE * 8; // 1 bit per data page


#[derive(Debug)]
pub enum Error {
    IllegalArgumentError(String),
    RuntimeError(String),
    PartitionNotFoundError(usize),
    PartitionAlreadyExistsError(usize),
    PageError(String),
    IOError(std::io::Error),
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::IllegalArgumentError(_) => match other {
                Self::IllegalArgumentError(_) => true,
                _ => false,
            },
            Self::RuntimeError(_) => match other {
                Self::RuntimeError(_) => true,
                _ => false,
            },
            Self::PartitionNotFoundError(_) => match other {
                Self::PartitionNotFoundError(_) => true,
                _ => false,
            },
            Self::PartitionAlreadyExistsError(_) => match other {
                Self::PartitionAlreadyExistsError(_) => true,
                _ => false,
            },
            Self::PageError(_) => match other {
                Self::PageError(_) => true,
                _ => false,
            },
            Self::IOError(_) => match other {
                Self::IOError(_) => true,
                _ => false,
            },
        }
    }
}

struct Partition {
    // Lock on the partition.
    lock: Mutex<()>,
    // Partition number
    part_num: usize,
    // Underlying OS file.
    file: File,
}

impl Partition {
    fn new(part_num: usize, file: File) -> Self {
        Self {
            lock: Mutex::new(()),
            part_num: part_num,
            file: file,
        }
    }

    // Allocates a new partition.
    fn alloc_part(&self) -> Result<(), Error> {
        let mut buf = BytesMut::with_capacity(PAGE_SIZE);
        for i in 0..MAX_HEADER_PAGES {
            buf.put_u16(0);
        }
        let mut f = BufWriter::new(&self.file);

        let offset = self.master_page_offset();
        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;

        f.write_all(&buf[..])
            .map(|_| Ok(()))
            .map_err(|e| Error::IOError(e))?
    }

    fn alloc_page(&self) -> Result<usize, Error> {
        // Partition size = master_num * PAGE_SIZE + header_num * PAGE_SIZE + data_num * PAGE_SIZE
        // master_num = 1
        // header_num = MAX_HEADER_PAGES
        // data_num = header_num * 8
        //
        // Offset (in pages):  0  1  2  3  4  5  6  7  8  9 10 11
        // Page Type:         [M][H][D][D][D][D][H][D][D][D][D][H]...
        // Header Index:          0              1              2
        // Data Page Index:          0  1  2  3     4  5  6  7
        let mut exists_free_page = false;
        let mut header_index = 0;
        let mut master_page_buf = BytesMut::zeroed(PAGE_SIZE);
        self.read_master_page(&mut master_page_buf)?;
        for i in 0..MAX_HEADER_PAGES {
            let header_page_num = master_page_buf.get_u16();
            if header_page_num < DATA_PAGES_PER_HEADER as u16 {
                header_index = i;
                exists_free_page = true;
                break;
            }
        }
        if !exists_free_page {
            return Err(Error::PageError("no free pages - partition has reached max size".to_string()));
        }

        let mut exists_page_space = false;
        let mut page_index = 0;
        let mut header_page_buf = BytesMut::zeroed(PAGE_SIZE);
        self.read_header_page(header_index, &mut header_page_buf)?;
        for (i, b) in header_page_buf.iter().enumerate()  {
            for n in 0..8 {
                if (!(b << n) & 0b10000000) == 0b10000000 {
                    page_index = (i*8) + n;
                    exists_page_space = true;
                    break;
                }
            }
            if exists_page_space {
                break;
            }
        }
        if !exists_page_space {
            return Err(Error::PageError("header page should have free space, but doesn't".to_string()));
        }

        self.alloc_page_with_index(header_index, page_index)
    }

    fn alloc_page_with_index(&self, header_index: usize, page_index: usize) -> Result<usize, Error> {
        if header_index > MAX_HEADER_PAGES {
            let msg = format!("over max header pages (header={})", header_index);
            return Err(Error::IllegalArgumentError(msg.to_string()))
        }
        if page_index > DATA_PAGES_PER_HEADER {
            let msg = format!("over max data pages (header={}, index={})", header_index, page_index);
            return Err(Error::IllegalArgumentError(msg.to_string()))
        }

        let mut master_page_buf = BytesMut::zeroed(PAGE_SIZE);
        self.read_master_page(&mut master_page_buf)?;

        let mut header_page_buf = BytesMut::zeroed(PAGE_SIZE);
        self.read_header_page(header_index, &mut header_page_buf)?;

        let mut bit_count: u16 = 0;
        for (i, b) in header_page_buf.iter_mut().enumerate()  {
            let start_page_index = i * 8;
            let end_page_index = (i+1) * 8;
            if start_page_index <= page_index && page_index < end_page_index {
                let n = page_index - start_page_index;
                if (*b << n & 0b10000000) == 0b10000000 {
                    let msg = format!("page at (part={}, header={}, index={}) already allocated", self.part_num, header_index, page_index);
                    return Err(Error::PageError(msg.to_string()))
                }
                *b = *b | (0b10000000 >> n);
            }
            bit_count += b.count_ones() as u16;
        }

        let bit_count = bit_count.to_be_bytes();

        master_page_buf[header_index*2] = bit_count[0];
        master_page_buf[header_index*2+1] = bit_count[1];

        let page_num = page_index + header_index * DATA_PAGES_PER_HEADER;

        self.write_master_page(&master_page_buf)?;
        self.write_header_page(header_index, &header_page_buf)?;

        Ok(page_num)
    }

    // Writes the master page to disk.
    fn write_master_page(&self, buf: &[u8]) -> Result<(), Error> {
        let offset = self.master_page_offset();
        let mut f = BufWriter::new(&self.file);

        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;

        f.write_all(&buf[..])
            .map(|_| Ok(()))
            .map_err(|e| Error::IOError(e))?
    }

    // Writes the header page to disk.
    fn write_header_page(&self, header_index: usize, buf: &[u8]) -> Result<(), Error> {
        let offset = self.header_page_offset(header_index);
        let mut f = BufWriter::new(&self.file);

        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;

        f.write_all(&buf[..])
            .map(|_| Ok(()))
            .map_err(|e| Error::IOError(e))?
    }

    // Writes the data page to disk.
    fn write_data_page(&self, page_num: usize, buf: &[u8]) -> Result<(), Error> {
        let offset = self.data_page_offset(page_num);
        let mut f = BufWriter::new(&self.file);

        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;

        f.write_all(&buf[..])
            .map(|_| Ok(()))
            .map_err(|e| Error::IOError(e))?
    }

    fn read_data_page(&self, page_num: usize, buf: &mut [u8]) -> Result<(), Error> {
        // if (this.isNotAllocatedPage(pageNum)) {
        //     throw new PageException("page " + pageNum + " is not allocated");
        // }
        let offset = self.data_page_offset(page_num);
        let mut f = BufReader::new(&self.file);
        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;
        f.read_exact(buf).map_err(|e| Error::IOError(e))?;
        Ok(())
    }

    fn read_master_page(&self, buf: &mut [u8]) -> Result<(), Error> {
        let offset = self.master_page_offset();
        let mut f = BufReader::new(&self.file);
        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;
        f.read_exact(buf).map_err(|e| Error::IOError(e))?;
        Ok(())
    }

    fn read_header_page(&self, header_index: usize, buf: &mut [u8]) -> Result<(), Error> {
        let offset = self.header_page_offset(header_index);
        let mut f = BufReader::new(&self.file);
        f.seek(SeekFrom::Start(offset as u64)).map_err(|e| Error::IOError(e))?;
        match f.read_exact(buf) {
            Ok(_) => Ok(()),
            Err(e) => match e.kind() {
                std::io::ErrorKind::UnexpectedEof => Ok(()),
                _ => Err(Error::IOError(e))
            },
        }
    }

    fn free_data_page(&self, page_num: usize) -> Result<(), Error> {
        let header_index = page_num / DATA_PAGES_PER_HEADER;
        let page_index = page_num % DATA_PAGES_PER_HEADER;

        let mut master_page_buf = BytesMut::zeroed(PAGE_SIZE);
        self.read_master_page(&mut master_page_buf)?;

        let mut header_page_buf = BytesMut::zeroed(PAGE_SIZE);
        self.read_header_page(header_index, &mut header_page_buf)?;

        let mut bit_count: u16 = 0;
        for (i, b) in header_page_buf.iter_mut().enumerate()  {
            let start_page_index = i * 8;
            let end_page_index = (i+1) * 8;
            if start_page_index <= page_index && page_index < end_page_index {
                let n = page_index - start_page_index;
                if ((!(*b) << n) & 0b10000000) == 0b10000000 {
                    return Err(Error::PageError("cannot free unallocated page".to_string()))
                }
                *b = !(!(*b) | (0b00000001 << n));
            }
            bit_count += b.count_ones() as u16;
        }

        let bit_count = bit_count.to_be_bytes();

        master_page_buf[header_index*2] = bit_count[0];
        master_page_buf[header_index*2+1] = bit_count[1];

        self.write_master_page(&master_page_buf)?;
        self.write_header_page(header_index, &header_page_buf)?;

        Ok(())
    }

    fn master_page_offset(&self) -> usize {
        0
    }

    fn header_page_offset(&self, header_index: usize) -> usize {
        // Consider the layout if we had 4 data pages per header:
        // Offset (in pages):  0  1  2  3  4  5  6  7  8  9 10 11
        // Page Type:         [M][H][D][D][D][D][H][D][D][D][D][H]...
        // Header Index:          0              1              2
        // To get the offset in pages of a header page you should add 1 for
        // the master page, and then take the header index times the number
        // of data pages per header plus 1 to account for the header page
        // itself (in the above example this coefficient would be 5)
        let spacing_coeff = DATA_PAGES_PER_HEADER + 1; // Promote to long
        (1 + header_index * spacing_coeff) * PAGE_SIZE
    }

    fn data_page_offset(&self, page_num: usize) -> usize {
        // Consider the layout if we had 4 data pages per header:
        // Offset (in pages):  0  1  2  3  4  5  6  7  8  9 10
        // Page Type:         [M][H][D][D][D][D][H][D][D][D][D]
        // Data Page Index:          0  1  2  3     4  5  6  7
        // To get the offset in pages of a given data page you should:
        // - add one for the master page
        // - add one for the first header page
        // - add how many other header pages precede the data page
        //   (found by floor dividing page num by data pages per header)
        // - add how many data pages precede the given data page
        //   (this works out conveniently to the page's page number)
        let other_headers = page_num / DATA_PAGES_PER_HEADER;
        (2 + other_headers + page_num) * PAGE_SIZE
    }
}

/**
 * An implementation of a disk space manager with virtual page translation, and
 * two levels of header pages, allowing for (with page size of 4K) 256G worth of data per partition:
 *
 *                                           [master page]
 *                  /                              |                               \
 *           [header page]                                                    [header page]
 *     /    |     |     |     \                   ...                   /    |     |     |     \
 * [data] [data] ... [data] [data]                                   [data] [data] ... [data] [data]
 *
 * Each header page stores a bitmap, indicating whether each of the data pages has been allocated,
 * and manages 32K pages. The master page stores 16-bit integers for each of the header pages indicating
 * the number of data pages that have been allocated under the header page (managing 2K header pages).
 * A single partition may therefore have a maximum of 64M data pages.
 *
 * Master and header pages are cached permanently in memory; changes to these are immediately flushed to
 * disk. This imposes a fairly small memory overhead (128M partitions have 2 pages cached). This caching
 * is done separately from the buffer manager's caching.
 *
 * Virtual page numbers are 64-bit integers (Java longs) assigned to data pages in the following format:
 *       partition number * 10^10 + n
 * for the n-th data page of the partition (indexed from 0). This particular format (instead of a simpler
 * scheme such as assigning the upper 32 bits to partition number and lower 32 to page number) was chosen
 * for ease of debugging (it's easier to read 10000000006 as part 1 page 6, than it is to decipher 4294967302).
 *
 * Partitions are backed by OS level files (one OS level file per partition), and are stored in the following
 * manner:
 * - the master page is the 0th page of the OS file
 * - the first header page is the 1st page of the OS file
 * - the next 32K pages are data pages managed by the first header page
 * - the second header page follows
 * - the next 32K pages are data pages managed by the second header page
 * - etc.
 */
pub struct DiskSpaceManager {
    // Lock on the entire manager.
    lock: Mutex<()>,
    // Name of base directory.
    db_dir: String,
    // Counter to generate new partition numbers.
    part_num: usize,
    // Info about each partition.
    part_info: HashMap<usize, Partition>,
}

impl DiskSpaceManager {
    pub fn new(db_dir: &str) -> Result<Self, Error> {
        if !Path::new(db_dir).exists() {
            std::fs::create_dir(db_dir).map_err(|e| Error::IOError(e))?;
        }

        let mut part_num: usize = 0;
        let mut part_info: HashMap<usize, Partition> =  HashMap::new();

        let part_paths = std::fs::read_dir(db_dir).map_err(|e| Error::IOError(e))?;
        for entry in part_paths {
            let entry = entry.map_err(|e| Error::IOError(e))?;
            let path = entry.path();
            if path.is_dir() {
                continue;
            }

            let part_file_name = path.file_name();
            if part_file_name.is_none() {
                continue;
            }
            let part_file_name = part_file_name.unwrap().to_str();
            if part_file_name.is_none() {
                continue;
            }
            let part_file_name = part_file_name.unwrap();
            let part_file_part_num: usize = match part_file_name.parse() {
                Ok(n) => n,
                Err(_) => continue,
            };

            let part_file = OpenOptions::new()
                .read(true)
                .write(true)
                .open(path)
                .map_err(|e| Error::IOError(e))?;

            let part = Partition::new(part_file_part_num, part_file);

            part_info.insert(part_file_part_num, part);
            part_num = std::cmp::max(part_num, part_file_part_num);
        }

        Ok(Self {
            lock: Mutex::new(()),
            db_dir: db_dir.to_string(),
            part_num: part_num,
            part_info: part_info,
        })
    }

    /**
     * Allocates a new partition.
     *
     * @return partition number of new partition
     */
    pub fn alloc_part(&mut self) -> Result<usize, Error> {
        let _lock = self.lock.lock().unwrap();

        let part_num = self.part_num;
        self.part_num += 1;

        if self.part_info.contains_key(&part_num) {
            return Err(Error::PartitionAlreadyExistsError(part_num));
        }

        let pi = self.new_partition(part_num)?;
        self.part_info.insert(part_num, pi);

        // TODO
        // We must open partition only after logging, but we need to release the
        // manager lock first, in case the log manager is currently in the process
        // of allocating a new log page (for another txn's records).

        Ok(part_num)
    }

    /**
     * Allocates a new partition with a specific partition number.
     *
     * @param partNum partition number of new partition
     * @return partition number of new partition
     */
    pub fn alloc_part_with_num(&mut self, part_num: usize) -> Result<usize, Error> {
        let _lock = self.lock.lock().unwrap();

        self.part_num = part_num + 1;

        if self.part_info.contains_key(&part_num) {
            return Err(Error::PartitionAlreadyExistsError(part_num));
        }

        let pi = self.new_partition(part_num)?;
        self.part_info.insert(part_num, pi);

        // TODO
        // We must open partition only after logging, but we need to release the
        // manager lock first, in case the log manager is currently in the process
        // of allocating a new log page (for another txn's records).

        Ok(part_num)
    }

    /**
     * Releases a partition from use.

     * @param partNum partition number to be released
     */
    pub fn free_part(&mut self, part_num: usize) -> Result<(), Error> {
        let _lock = self.lock.lock().unwrap();

        match self.part_info.remove(&part_num) {
            Some(pi) => pi,
            None => return Err(Error::PartitionNotFoundError(part_num)),
        };

        std::fs::remove_file(self.part_file_path(part_num))
            .map(|_| Ok(()))
            .map_err(|e| Error::IOError(e))?
    }

    /**
     * Allocates a new page.
     * @param partNum partition to allocate new page under
     * @return virtual page number of new page
     */
    pub fn alloc_page(&self, part_num: usize) -> Result<usize, Error> {
        let _lock = self.lock.lock().unwrap();

        let pi = match self.part_info.get(&part_num) {
            Some(pi) => pi,
            None => return Err(Error::PartitionNotFoundError(part_num)),
        };

        let page_num = pi.alloc_page()?;
        let buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        pi.write_data_page(page_num, &buf)?;

        Ok(Self::get_virtual_page_num(part_num, page_num))
    }

    /**
     * Allocates a new page with a specific page number.
     * @param pageNum page number of new page
     * @return virtual page number of new page
     */
    pub fn alloc_page_with_page(&self, page: usize) -> Result<usize, Error> {
        let part_num = Self::get_part_num(page);
        let page_num = Self::get_page_num(page);
        let header_index = page_num / DATA_PAGES_PER_HEADER;
        let page_index = page_num % DATA_PAGES_PER_HEADER;

        let _lock = self.lock.lock().unwrap();

        let pi = match self.part_info.get(&part_num) {
            Some(pi) => pi,
            None => return Err(Error::PartitionNotFoundError(part_num)),
        };

        let page_num = pi.alloc_page_with_index(header_index, page_index)?;
        let buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        pi.write_data_page(page_num, &buf)?;

        Ok(Self::get_virtual_page_num(part_num, page_num))
    }

    /**
     * Frees a page. The page cannot be used after this call.
     * @param page virtual page number of page to be released
     */
    pub fn free_page(&self, page: usize) -> Result<(), Error> {
        let part_num = Self::get_part_num(page);
        let page_num = Self::get_page_num(page);

        let _lock = self.lock.lock().unwrap();

        let pi = match self.part_info.get(&part_num) {
            Some(pi) => pi,
            None => return Err(Error::PartitionNotFoundError(part_num)),
        };

        pi.free_data_page(page_num)
            .map_err(|e| match e {
                Error::IOError(ie) => {
                    let msg = format!("could not modify partition {}: {}", part_num, ie);
                    Error::PageError(msg)
                },
                _ => e,
            })?;

        Ok(())
    }

    /**
     * Reads a page.
     *
     * @param page number of page to be read
     * @param buf byte buffer whose contents will be filled with page data
     */
    pub fn read_page(&self, page: usize, buf: &mut [u8]) -> Result<(), Error> {
        if buf.len() != PAGE_SIZE {
            return Err(Error::IllegalArgumentError("readPage expects a page-sized buffer".to_string()));
        }

        let _lock = self.lock.lock().unwrap();

        let part_num = Self::get_part_num(page);
        let page_num = Self::get_page_num(page);

        let pi = match self.part_info.get(&part_num) {
            Some(pi) => pi,
            None => return Err(Error::PartitionNotFoundError(part_num)),
        };

        pi.read_data_page(page_num, buf)
            .map_err(|e| match e {
                Error::IOError(ie) => {
                    let msg = format!("could not read partition {}: {}", part_num, ie);
                    Error::PageError(msg)
                },
                _ => e,
            })?;

        Ok(())
    }

    /**
     * Writes to a page.
     *
     * @param page number of page to be read
     * @param buf byte buffer that contains the new page data
     */
    pub fn write_page(&self, page: usize, buf: &[u8]) -> Result<(), Error> {
        if buf.len() != PAGE_SIZE {
            return Err(Error::IllegalArgumentError("readPage expects a page-sized buffer".to_string()));
        }

        let _lock = self.lock.lock().unwrap();

        let part_num = Self::get_part_num(page);
        let page_num = Self::get_page_num(page);

        let pi = match self.part_info.get(&part_num) {
            Some(pi) => pi,
            None => return Err(Error::PartitionNotFoundError(part_num)),
        };

        pi.write_data_page(page_num, buf)
            .map_err(|e| match e {
                Error::IOError(ie) => {
                    let msg = format!("could not write partition {}: {}", part_num, ie);
                    Error::PageError(msg)
                },
                _ => e,
            })?;

        Ok(())
    }

    /**
     * Checks if a page is allocated
     *
     * @param page number of page to check
     * @return true if the page is allocated, false otherwise
     */
    pub fn page_allocated(&self, page: usize) -> bool {
        false
    }

    /**
     * Gets partition number from virtual page number
     * @param page virtual page number
     * @return partition number
     */
    pub fn get_part_num(page: usize) -> usize {
        page / 10000000000
    }

    /**
     * Gets data page number from virtual page number
     * @param page virtual page number
     * @return data page number
     */
    pub fn get_page_num(page: usize) -> usize {
        page % 10000000000
    }

    /**
     * Gets the virtual page number given partition/data page number
     * @param partNum partition number
     * @param pageNum data page number
     * @return virtual page number
     */
    pub fn get_virtual_page_num(part_num: usize, page_num: usize) -> usize {
        part_num * 10000000000 + page_num
    }

    fn part_file_path(&self, part_num: usize) -> PathBuf {
        Path::new(&self.db_dir).join(format!("{}", part_num))
    }

    fn new_partition(&self, part_num: usize) -> Result<Partition, Error> {
        let part_file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(self.part_file_path(part_num))
            .map_err(|e| Error::IOError(e))?;

        let part = Partition::new(part_num, part_file);
        part.alloc_part();

        Ok(part)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    fn setup() {
        let db_dir = get_db_dir();
        if db_dir.exists() {
            std::fs::remove_dir_all(std::env::temp_dir().join("dsm-test"));
        }
    }

    fn get_db_dir() -> PathBuf {
        std::env::temp_dir().join("dsm-test")
    }

    fn get_disk_space_manager() -> DiskSpaceManager {
        let db_dir_buf = get_db_dir();
        let db_dir = db_dir_buf.as_os_str().to_str().unwrap();
        DiskSpaceManager::new(db_dir).unwrap()
    }

    #[test]
    #[serial]
    fn test_alloc_part() {
        setup();

        let db_dir = get_db_dir();
        let mut disk_space_manager = get_disk_space_manager();

        let part_num = disk_space_manager.alloc_part_with_num(0);

        assert!(!part_num.is_err());
        assert_eq!(0, part_num.unwrap());
        assert!(db_dir.join("0").exists());
        assert_eq!(PAGE_SIZE as u64, File::open(db_dir.join("0")).unwrap().metadata().unwrap().len());

        let part_num = disk_space_manager.alloc_part();
        assert!(!part_num.is_err());
        assert_eq!(1, part_num.unwrap());
        assert!(db_dir.join("1").exists());
        assert_eq!(PAGE_SIZE as u64, File::open(db_dir.join("1")).unwrap().metadata().unwrap().len());
    }

    #[test]
    #[serial]
    fn test_free_part_not_exists() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();

        let result = disk_space_manager.free_part(1);
        assert!(result.is_err());
        assert_eq!(Error::PartitionNotFoundError(1), result.unwrap_err());
    }


    #[test]
    #[serial]
    fn test_free_part() {
        setup();

        let db_dir = get_db_dir();
        let mut disk_space_manager = get_disk_space_manager();

        let part_num = disk_space_manager.alloc_part().unwrap();
        let result = disk_space_manager.free_part(part_num);
        assert!(result.is_ok());
        assert!(!db_dir.join("0").exists());
    }

    #[test]
    #[serial]
    fn test_free_part_persist() {
        setup();

        let db_dir = get_db_dir();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num = disk_space_manager.alloc_part().unwrap();
        disk_space_manager.free_part(part_num).unwrap();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num = disk_space_manager.alloc_part().unwrap();
        assert_eq!(0, part_num);
        assert!(db_dir.join("0").exists());
        assert!(!db_dir.join("1").exists());
    }

    #[test]
    #[serial]
    fn test_alloc_page_zeroed() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();

        let part_num = disk_space_manager.alloc_part_with_num(0).unwrap();
        let page_num1 = disk_space_manager.alloc_page(part_num).unwrap();
        let page_num2 = disk_space_manager.alloc_page_with_page(1).unwrap();

        assert_eq!(0, page_num1);
        assert_eq!(1, page_num2);

        let expected_zero_buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        disk_space_manager.read_page(page_num1, &mut buf);
        assert_eq!(expected_zero_buf, buf);
        disk_space_manager.read_page(page_num2, &mut buf);
        assert_eq!(expected_zero_buf, buf);

        let page_num3 = disk_space_manager.alloc_page(part_num).unwrap();
        let page_num4 = disk_space_manager.alloc_page(part_num).unwrap();

        let mut disk_space_manager = get_disk_space_manager();
        let mut buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        disk_space_manager.read_page(page_num1, &mut buf);
        assert_eq!(expected_zero_buf, buf);
        disk_space_manager.read_page(page_num2, &mut buf);
        assert_eq!(expected_zero_buf, buf);
        disk_space_manager.read_page(page_num3, &mut buf);
        assert_eq!(expected_zero_buf, buf);
        disk_space_manager.read_page(page_num4, &mut buf);
        assert_eq!(expected_zero_buf, buf);
    }

    #[test]
    #[serial]
    fn test_read_bad_part() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();

        let mut buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let result = disk_space_manager.read_page(0, &mut buf);

        assert!(result.is_err());
        assert_eq!(Error::PartitionNotFoundError(0), result.unwrap_err());
    }

    #[test]
    #[serial]
    fn test_read_bad_buffer() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();

        let mut buf: [u8; PAGE_SIZE-1] = [0; PAGE_SIZE-1];
        let result = disk_space_manager.read_page(0, &mut buf);

        assert!(result.is_err());
        assert_eq!(Error::IllegalArgumentError("".to_string()), result.unwrap_err());
    }

    #[test]
    #[serial]
    fn test_read_out_of_bounds() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num = disk_space_manager.alloc_part().unwrap();

        let mut buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let result = disk_space_manager.read_page(0, &mut buf);

        assert!(result.is_err());
        assert_eq!(Error::PageError("".to_string()), result.unwrap_err());
    }

    #[test]
    #[serial]
    fn test_read_write() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num = disk_space_manager.alloc_part().unwrap();
        let page_num = disk_space_manager.alloc_page(part_num).unwrap();

        let mut buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        rand::thread_rng().fill_bytes(&mut buf);
        disk_space_manager.write_page(page_num, &buf).unwrap();

        let mut read_buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        disk_space_manager.read_page(page_num, &mut read_buf).unwrap();
        assert_eq!(buf, read_buf);
    }

    #[test]
    #[serial]
    fn test_read_write_persistent() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num = disk_space_manager.alloc_part().unwrap();
        let page_num = disk_space_manager.alloc_page(part_num).unwrap();

        let mut buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        rand::thread_rng().fill_bytes(&mut buf);
        disk_space_manager.write_page(page_num, &buf).unwrap();

        let mut disk_space_manager = get_disk_space_manager();
        let mut read_buf: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        disk_space_manager.read_page(page_num, &mut read_buf).unwrap();

        assert_eq!(buf, read_buf);
    }

    #[test]
    #[serial]
    fn test_read_write_multiple_partitions() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num1 = disk_space_manager.alloc_part().unwrap();
        let part_num2 = disk_space_manager.alloc_part().unwrap();
        let page_num11 = disk_space_manager.alloc_page(part_num1).unwrap();
        let page_num21 = disk_space_manager.alloc_page(part_num2).unwrap();
        let page_num22 = disk_space_manager.alloc_page(part_num2).unwrap();

        let mut buf11: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut buf21: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut buf22: [u8; PAGE_SIZE] = [0; PAGE_SIZE];

        rand::thread_rng().fill_bytes(&mut buf11);
        rand::thread_rng().fill_bytes(&mut buf21);
        rand::thread_rng().fill_bytes(&mut buf22);

        disk_space_manager.write_page(page_num11, &buf11).unwrap();
        disk_space_manager.write_page(page_num21, &buf21).unwrap();
        disk_space_manager.write_page(page_num22, &buf22).unwrap();

        let mut read_buf11: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut read_buf21: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut read_buf22: [u8; PAGE_SIZE] = [0; PAGE_SIZE];

        disk_space_manager.read_page(page_num11, &mut read_buf11).unwrap();
        disk_space_manager.read_page(page_num21, &mut read_buf21).unwrap();
        disk_space_manager.read_page(page_num22, &mut read_buf22).unwrap();

        assert_eq!(buf11, read_buf11);
        assert_eq!(buf21, read_buf21);
        assert_eq!(buf22, read_buf22);
    }

    #[test]
    #[serial]
    fn test_read_write_multiple_partitions_persistent() {
        setup();

        let mut disk_space_manager = get_disk_space_manager();
        let part_num1 = disk_space_manager.alloc_part().unwrap();
        let part_num2 = disk_space_manager.alloc_part().unwrap();
        let page_num11 = disk_space_manager.alloc_page(part_num1).unwrap();
        let page_num21 = disk_space_manager.alloc_page(part_num2).unwrap();
        let page_num22 = disk_space_manager.alloc_page(part_num2).unwrap();

        let mut buf11: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut buf21: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut buf22: [u8; PAGE_SIZE] = [0; PAGE_SIZE];

        rand::thread_rng().fill_bytes(&mut buf11);
        rand::thread_rng().fill_bytes(&mut buf21);
        rand::thread_rng().fill_bytes(&mut buf22);

        disk_space_manager.write_page(page_num11, &buf11).unwrap();
        disk_space_manager.write_page(page_num21, &buf21).unwrap();
        disk_space_manager.write_page(page_num22, &buf22).unwrap();

        let mut disk_space_manager = get_disk_space_manager();

        let mut read_buf11: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut read_buf21: [u8; PAGE_SIZE] = [0; PAGE_SIZE];
        let mut read_buf22: [u8; PAGE_SIZE] = [0; PAGE_SIZE];

        disk_space_manager.read_page(page_num11, &mut read_buf11).unwrap();
        disk_space_manager.read_page(page_num21, &mut read_buf21).unwrap();
        disk_space_manager.read_page(page_num22, &mut read_buf22).unwrap();

        assert_eq!(buf11, read_buf11);
        assert_eq!(buf21, read_buf21);
        assert_eq!(buf22, read_buf22);
    }
}
