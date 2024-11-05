use core::str::FromStr;

use heapless::{String, Vec};

use crate::map::{Key, SerializationError, Value};

// heapless:: Vec

impl<const CAP: usize> Key for Vec<u8, CAP> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() + 2 {
            return Err(SerializationError::BufferTooSmall);
        }

        if self.len() > u16::MAX as usize {
            return Err(SerializationError::InvalidData);
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

        let mut output = Vec::new();
        output
            .extend_from_slice(&buffer[2..][..data_len])
            .map_err(|_| SerializationError::InvalidFormat)?;

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

impl<'a, const CAP: usize> Value<'a> for Vec<u8, CAP> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() {
            return Err(SerializationError::BufferTooSmall);
        }

        buffer[..self.len()].copy_from_slice(self.as_slice());
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<Self, SerializationError>
    where
        Self: Sized,
    {
        Vec::try_from(buffer).map_err(|_| SerializationError::InvalidFormat)
    }
}

// heapless::String

impl<const CAP: usize> Key for String<CAP> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() + 2 {
            return Err(SerializationError::InvalidFormat);
        }

        if self.len() > u16::MAX as usize {
            return Err(SerializationError::InvalidData);
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

        let mut output = String::new();
        output
            .push_str(
                core::str::from_utf8(&buffer[2..][..data_len])
                    .map_err(|_| SerializationError::InvalidFormat)?,
            )
            .map_err(|_| SerializationError::InvalidFormat)?;

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

impl<'a, const CAP: usize> Value<'a> for String<CAP> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() {
            return Err(SerializationError::BufferTooSmall);
        }

        buffer[..self.len()].copy_from_slice(self.as_bytes());
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<Self, SerializationError>
    where
        Self: Sized,
    {
        let output = String::from_str(
            core::str::from_utf8(buffer).map_err(|_| SerializationError::InvalidFormat)?,
        )
        .map_err(|_| SerializationError::BufferTooSmall)?;

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn key_serde_heapless_vec() {
        let mut buffer = [0; 128];

        let val = Vec::<u8, 12>::from_iter([0xAA; 12]);
        Key::serialize_into(&val, &mut buffer).unwrap();
        let new_val = <Vec<u8, 12> as Key>::deserialize_from(&buffer).unwrap();

        assert_eq!((val, 14), new_val);
    }

    #[test]
    fn key_serde_heapless_string() {
        let mut buffer = [0; 128];

        let val = String::<45>::from_str("Hello world!").unwrap();
        Key::serialize_into(&val, &mut buffer).unwrap();
        let new_val = <String<45> as Key>::deserialize_from(&buffer).unwrap();

        assert_eq!((val, 14), new_val);
    }

    #[test]
    fn value_serde_heapless_vec() {
        let mut buffer = [0; 12];

        let val = Vec::<u8, 12>::from_iter([0xAA; 12]);
        Value::serialize_into(&val, &mut buffer).unwrap();
        let new_val = <Vec<u8, 12> as Value>::deserialize_from(&buffer).unwrap();

        assert_eq!(val, new_val);
    }

    #[test]
    fn value_serde_heapless_string() {
        let mut buffer = [0; 12];

        let val = String::<45>::from_str("Hello world!").unwrap();
        Value::serialize_into(&val, &mut buffer).unwrap();
        let new_val = <String<45> as Value>::deserialize_from(&buffer).unwrap();

        assert_eq!(val, new_val);
    }
}
