extern crate alloc;
use crate::map::{Key, SerializationError, Value};
use alloc::{string::String, vec::Vec};

// alloc::Vec

impl Key for Vec<u8> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if self.len() > u16::MAX as usize {
            return Err(SerializationError::InvalidData);
        }

        if buffer.len() < self.len() + 2 {
            return Err(SerializationError::BufferTooSmall);
        }

        buffer[..2].copy_from_slice(&(self.len() as u16).to_le_bytes());
        buffer[2..][..self.len()].copy_from_slice(self);

        Ok(self.len() + 2)
    }

    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
        let total_len = Self::get_len(buffer)?;

        if buffer.len() < total_len {
            return Err(SerializationError::BufferTooSmall);
        }

        let data_len = total_len - 2;

        let output = Vec::from(&buffer[2..][..data_len]);

        Ok((output, total_len))
    }

    fn get_len(buffer: &[u8]) -> Result<usize, SerializationError> {
        if buffer.len() < 2 {
            return Err(SerializationError::BufferTooSmall);
        }

        let len = u16::from_le_bytes(buffer[..2].try_into().unwrap());

        Ok(len as usize + 2)
    }
}

impl<'a> Value<'a> for Vec<u8> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() {
            return Err(SerializationError::BufferTooSmall);
        }

        buffer[..self.len()].copy_from_slice(self.as_slice());
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<(Self, usize), SerializationError>
    where
        Self: Sized,
    {
        Ok((Vec::from(buffer), buffer.len()))
    }
}

// alloc::String

impl Key for String {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if self.len() > u16::MAX as usize {
            return Err(SerializationError::InvalidData);
        }

        if buffer.len() < self.len() + 2 {
            return Err(SerializationError::BufferTooSmall);
        }

        buffer[..2].copy_from_slice(&(self.len() as u16).to_le_bytes());
        buffer[2..][..self.len()].copy_from_slice(self.as_bytes());

        Ok(self.len() + 2)
    }

    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
        let total_len = Self::get_len(buffer)?;

        if buffer.len() < total_len {
            return Err(SerializationError::BufferTooSmall);
        }

        let data_len = total_len - 2;

        let output = String::from(
            core::str::from_utf8(&buffer[2..][..data_len])
                .map_err(|_| SerializationError::InvalidFormat)?,
        );

        Ok((output, total_len))
    }

    fn get_len(buffer: &[u8]) -> Result<usize, SerializationError> {
        if buffer.len() < 2 {
            return Err(SerializationError::BufferTooSmall);
        }

        let len = u16::from_le_bytes(buffer[..2].try_into().unwrap());

        Ok(len as usize + 2)
    }
}

impl<'a> Value<'a> for String {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() {
            return Err(SerializationError::BufferTooSmall);
        }

        buffer[..self.len()].copy_from_slice(self.as_bytes());
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<(Self, usize), SerializationError>
    where
        Self: Sized,
    {
        let output = String::from(
            core::str::from_utf8(buffer).map_err(|_| SerializationError::InvalidFormat)?,
        );

        Ok((output, buffer.len()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_serde_alloc_vec() {
        let mut buffer = [0; 128];

        let val = Vec::from_iter([0xAAu8; 12]);
        Key::serialize_into(&val, &mut buffer).unwrap();
        let new_val = <Vec<_> as Key>::deserialize_from(&buffer).unwrap();

        assert_eq!((val, 14), new_val);
    }

    #[test]
    fn key_serde_alloc_string() {
        let mut buffer = [0; 128];

        let val = String::from("Hello world!");
        Key::serialize_into(&val, &mut buffer).unwrap();
        let new_val = <String as Key>::deserialize_from(&buffer).unwrap();

        assert_eq!((val, 14), new_val);
    }

    #[test]
    fn value_serde_alloc_vec() {
        let mut buffer = [0; 12];

        let val = Vec::from_iter([0xAAu8; 12]);
        Value::serialize_into(&val, &mut buffer).unwrap();
        let (new_val, size) = <Vec<_> as Value>::deserialize_from(&buffer).unwrap();

        assert_eq!(val, new_val);
        assert_eq!(size, 12);
    }

    #[test]
    fn value_serde_alloc_string() {
        let mut buffer = [0; 12];

        let val = String::from("Hello world!");
        Value::serialize_into(&val, &mut buffer).unwrap();
        let (new_val, size) = <String as Value>::deserialize_from(&buffer).unwrap();

        assert_eq!(val, new_val);
        assert_eq!(size, 12);
    }
}
