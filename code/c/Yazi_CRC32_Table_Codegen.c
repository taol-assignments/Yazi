#include <stdio.h>
#include <stdint.h>
#include "Yazi_CRC32_Table.h"

int main(int argc, const char **argv) {
  uint32_t table[4][256];
  gen_crc32_table(table[0], table[1], table[2], table[3]);

  uint32_t matrix[32];
  gen_matrix_table(matrix);

  printf("static uint32_t crc32_table[4][256] = {\n");
  
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

  printf(
    "\n};\n\n"
    "uint32_t crc32_combine64(uint32_t crc1, uint32_t crc2, uint64_t len2) {\n"
    "  uint32_t m0[32];\n"
    "  uint32_t m1[32] = {\n");

  for (int i = 0; i < 32; i++) {
    printf("0x%.8xUL, ", matrix[i]);
    if (i > 0 && i % 5 == 0) {
      printf("\n  ");
    }
  }
  
  printf(
    "  \n};\n"
    "  if (len2 == 0) {\n"
    "    return crc1;\n"
    "  }\n\n"
    "  for (;;) {\n"
    "    if (len2 & 1) {\n"
    "      crc1 = Yazi_CRC32_Impl_gf2_matrix_times((uint32_t *)m1, crc1);\n"
    "    }\n\n"
    "    len2 >>= 1;\n"
    "    if (len2 > 0) {\n"
    "      Yazi_CRC32_Impl_gf2_matrix_square((uint32_t *)m1, (uint32_t *)m0);\n"
    "      if (len2 & 1) {\n"
    "        crc1 = Yazi_CRC32_Impl_gf2_matrix_times((uint32_t *)m0, crc1);\n"
    "      }\n"
    "      len2 >>= 1;\n"
    "      if (len2 > 0) {\n"
    "        Yazi_CRC32_Impl_gf2_matrix_square((uint32_t *)m0, (uint32_t *)m1);\n"
    "      } else {\n"
    "        break;\n"
    "      }\n"
    "    } else {\n"
    "      break;\n"
    "    }\n"
    "  }\n\n"
    "  return crc1 ^ crc2;\n}\n\n"
    "uint32_t crc32_combine(uint32_t crc1, uint32_t crc2, uint32_t len2) {\n"
    "  return crc32_combine64(crc1, crc2, len2);\n"
    "}\n\n"
    "unsigned int crc32(unsigned int crc, const unsigned char *buf, unsigned int len) {\n"
    "  return Yazi_CRC32_Impl_crc32_impl((uint32_t *)crc32_table, crc, len, (uint8_t *) buf);\n"
    "}\n");

  return 0;
}

