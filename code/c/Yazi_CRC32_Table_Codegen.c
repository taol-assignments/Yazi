#include <stdio.h>
#include <stdint.h>
#include "Yazi_CRC32.h"

int main(int argc, const char **argv) {
  uint32_t matrix[32];
  uint32_t table[4][256];
  
  gen_crc32_table(table[0], table[1], table[2], table[3]);
  gen_matrix_table(matrix);

  printf(
    "#ifndef __GNUC__\n"
    "#include <stddef.h>\n"
    "#include <string.h>\n"
    "#else\n"
    "typedef __SIZE_TYPE__ size_t;\n"
    "#endif\n"
    "#include \"Yazi_CRC32.h\"\n"
    "#include \"Yazi_CRC32_Z.inc\"\n\n"
    "static const uint32_t crc32_table[4][256] = {\n");
  
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
      printf("%uu, ", table[i][j]);
    }
    printf("\n  }");
    if (i != 3) {
      printf(", ");
    }
  }

  printf(
    "\n};\n\n"
    "static const uint32_t magic_matrix[32] = {");

  for (int i = 0; i < 32; i++) {
    if (i % 5 == 0) {
      printf("\n  ");
    }
    printf("%uu, ", matrix[i]);
  }

  printf(
    "\n};\n\n"
    "static inline const uint32_t *get_crc32_table(uint32_t i) {\n"
    "  return crc32_table[i];\n"
    "}\n\n"
    "static inline void init_magic_matrix(uint32_t *m) {\n");
  
  printf(
    "#ifdef __GNUC__\n"
    "  __builtin_memcpy(m, magic_matrix, sizeof(magic_matrix));\n"
    "#else\n"
    "  memcpy(m, magic_matrix, sizeof(magic_matrix));\n"
    "#endif\n"
    "}\n");

  return 0;
}

