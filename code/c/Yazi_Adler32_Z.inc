uint32_t adler32_z(uint32_t adler, const unsigned char *buf, size_t len) {
  while (len > 0xFFFFFFFFUL) {
    adler = adler32(adler, (unsigned char *)buf, 0xFFFFFFFFUL);
    buf += 0xFFFFFFFFUL;
    len -= 0xFFFFFFFFUL;
  }

  if (len > 0) {
    adler = adler32(adler, (unsigned char *)buf, len);
  }

  return adler;
}