#define Yazi_LZ77_ctz_compare(len, s, m, i) \
((len) == 4U ? do_ctz_compare_4((s) + i, (m) + i) : do_ctz_compare_8((s) + i, (m) + i))

static inline int is_little_endian(void)
{
  union {
    unsigned int v;
    unsigned char b;
  } u;
  u.v = 1;
  return u.b;
}

#define do_cmp(s, m, l) \
do {                    \
  if (*(s) != *(m)) {   \
    return l;           \
  } else {              \
    (s)++;              \
    (m)++;              \
  }                     \
} while (0)

#define do_cmp_end(s, m, l) \
do {                        \
  if (*(s) == *(m)) {       \
    return (l) + 1U;        \
  } else {                  \
    return l;               \
  }                         \
} while (0)

static inline uint32_t do_ctz_compare_4(uint8_t *s, uint8_t *m) {
#if defined __GNUC__ || defined __COMPCERT__
  unsigned int a, b;
  __builtin_memcpy(&a, s, sizeof(a));
  __builtin_memcpy(&b, m, sizeof(b));
  a ^= b;
  
  if (is_little_endian()) {
    return a == 0 ? 4U : (uint32_t)(__builtin_ctz(a) / 8);
  } else {
    return a == 0 ? 4U : (uint32_t)(__builtin_clz(a) / 8);
  }
#elif defined _MSC_VER
  unsigned int a, b;
  unsigned long index;
  memcpy(&a, s, sizeof(a));
  memcpy(&b, m, sizeof(b));
  a ^= b;

  if (is_little_endian()) {
    if (_BitScanForward(&index, a ^ b)) {
      return index / 8;
    } else {
      return 4U;
    }
  } else {
    if (_BitScanReverse(&index, a ^ b)) {
      return (31 - index) / 8;
    } else {
      return 4U;
    }
  }
#else
  do_cmp(s, m, 0U);
  do_cmp(s, m, 1U);
  do_cmp(s, m, 2U);
  do_cmp_end(s, m, 3U);
#endif
}

static inline uint32_t do_ctz_compare_8(uint8_t *s, uint8_t *m) {
#if defined __GNUC__ || defined __COMPCERT__
  unsigned long long a, b;
  __builtin_memcpy(&a, s, sizeof(a));
  __builtin_memcpy(&b, m, sizeof(b));
  a ^= b;
  
  if (is_little_endian()) {
    return a == 0 ? 8U : (uint32_t)(__builtin_ctzll(a) / 8);
  } else {
    return a == 0 ? 8U : (uint32_t)(__builtin_clzll(a) / 8);
  }
#elif defined _MSC_VER
  unsigned long long a, b, index;
  memcpy(&a, s, sizeof(a));
  memcpy(&b, m, sizeof(b));

  if (is_little_endian()) {
    if (_BitScanForward64(&index, a ^ b)) {
      return index / 8;
    } else {
      return 8U;
    }
  } else {
    if (_BitScanReverse64(&index, a ^ b)) {
      return (63 - index) / 8;
    } else {
      return 8U;
    }
  }
#else
  do_cmp(s, m, 0U);
  do_cmp(s, m, 1U);
  do_cmp(s, m, 3U);
  do_cmp(s, m, 4U);
  do_cmp(s, m, 5U);
  do_cmp(s, m, 6U);
  do_cmp_end(s, m, 7U);
#endif
}

#undef do_cmp
#undef do_cmp_end
