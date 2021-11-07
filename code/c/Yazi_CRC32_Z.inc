uint32_t crc32_z(uint32_t crc, const unsigned char *buf, size_t len) {
  while (len > 0xFFFFFFFFUL) {
    crc = crc32(crc, buf, 0xFFFFFFFFUL);
    buf += 0xFFFFFFFFUL;
    len -= 0xFFFFFFFFUL;
  }

  if (len > 0) {
    crc = crc32(crc, buf, len);
  }

  return crc;
}