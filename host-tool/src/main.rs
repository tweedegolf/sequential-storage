use std::{
    fs::File,
    io::{Read, Seek, SeekFrom},
    ops::Range,
};

use embedded_storage_async::nor_flash::{
    ErrorType, MultiwriteNorFlash, NorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash,
};
use sequential_storage::{cache::NoCache, Storage};

pub struct Partition(File);

impl Partition {
    pub const WORD_SIZE: usize = 4;
    pub const SECTOR_SIZE: usize = 4096;

    pub fn new(path: &str) -> Self {
        Self(File::open(path).unwrap())
    }
}

#[derive(Debug)]
pub struct Error(std::io::Error);
impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Self(value)
    }
}

impl NorFlashError for Error {
    fn kind(&self) -> NorFlashErrorKind {
        // match self.0.code() {
        //  => NorFlashErrorKind::NotAligned,
        // ESP_ERR_INVALID_SIZE => NorFlashErrorKind::OutOfBounds,
        // _ =>
        NorFlashErrorKind::Other
        // }
    }
}

impl ErrorType for Partition {
    type Error = Error;
}

impl ReadNorFlash for Partition {
    const READ_SIZE: usize = Self::WORD_SIZE as _;

    async fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        self.0.seek(SeekFrom::Start(offset as u64))?;
        self.0.read_exact(bytes).map_err(Error::from)
    }

    fn capacity(&self) -> usize {
        self.0.metadata().unwrap().len() as usize
    }
}

impl NorFlash for Partition {
    const WRITE_SIZE: usize = Self::WORD_SIZE as _;
    const ERASE_SIZE: usize = Self::SECTOR_SIZE as _;

    async fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        println!(
            "esp partition write at {:#x} size {:#x}",
            offset,
            bytes.len()
        );
        Ok(())
    }

    async fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        println!("esp partition erase from {:#x} size {:#x}", from, to - from);
        Ok(())
    }
}

impl MultiwriteNorFlash for Partition {}

#[tokio::main]
async fn main() -> Result<(), sequential_storage::Error<Error>> {
    let mut flash = Partition::new("rmk.raw");
    let flash_range: Range<u32> = 0..flash.capacity() as u32;
    let mut cache = NoCache::new();
    let mut storage = Storage::new(&mut flash, flash_range, &mut cache);

    let mut pageit = storage.iter().await?;
    while let Some(mut itemit) = pageit.next(&mut storage).await? {
        println!("Page {:?}", 1);
        let mut buffer = [0u8; 1024];
        while let Ok(Some((item, _))) = itemit.next(&mut storage.flash, &mut buffer).await {
            println!("\tItem {:02x?}", item.data());
        }
    }
    Ok(())
}
