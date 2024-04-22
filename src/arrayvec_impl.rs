use arrayvec::{ArrayString, ArrayVec};

use crate::map::{Key, SerializationError};

impl<const CAP: usize> Key for ArrayVec<u8, CAP> {
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

        let mut output = ArrayVec::new();
        output
            .try_extend_from_slice(&buffer[2..][..data_len])
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

impl<const CAP: usize> Key for ArrayString<CAP> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if buffer.len() < self.len() + 2 {
            return Err(SerializationError::BufferTooSmall);
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

        let mut output = ArrayString::new();
        output
            .try_push_str(
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

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::*;

    #[test]
    fn serde_arrayvec() {
        let mut buffer = [0; 128];

        let val = ArrayVec::<u8, 12>::from_iter([0xAA; 12]);
        val.serialize_into(&mut buffer).unwrap();
        let new_val = ArrayVec::<u8, 12>::deserialize_from(&buffer).unwrap();

        assert_eq!((val, 14), new_val);
    }

    #[test]
    fn serde_arraystring() {
        let mut buffer = [0; 128];

        let val = ArrayString::<45>::from_str("Hello world!").unwrap();
        val.serialize_into(&mut buffer).unwrap();
        let new_val = ArrayString::<45>::deserialize_from(&buffer).unwrap();

        assert_eq!((val, 14), new_val);
    }
}
