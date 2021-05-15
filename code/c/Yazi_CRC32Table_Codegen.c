#include <stdio.h>
#include <stdint.h>
#include "Yazi_CRC32Table.h"

int main(int argc, const char **argv) {
  uint32_t table[4][256];
  gen_crc32_table(table[0], table[1], table[2], table[3]);

  for (int i = 0; i < 1; i++) {
    for (int j = 0; j < 256; j++) { 
      printf("0x%.8x ", table[i][j]);
    }
  }
  
  return 0;
}
