#include <stdio.h>
#include <stdint.h>
#include "Yazi_CRC32Table.h"

int main(int argc, const char **argv) {
  uint32_t table[4][256];
  gen_crc32_table(table[0], table[1], table[2], table[3]);

  printf("uint32_t crc32_table[4][256] = {\n");
  
  for (int i = 0; i < 4; i++) {
    if (i == 0) {
      printf("  {");
    } else {
      printf("{");
    }
    for (int j = 0; j < 256; j++) {
      if (j % 5 == 0) {
	printf("\n    ");
      }
      printf("0x%.8xUL, ", table[i][j]);
    }
    printf("\n  }");
    if (i != 3) {
      printf(", ");
    }
  }
  
  printf("\n};\n");
  
  return 0;
}