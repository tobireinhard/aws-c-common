/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/private/byte_buf.h>

#include <stdarg.h>

#ifdef _MSC_VER
/* disables warning non const declared initializers for Microsoft compilers */
#    pragma warning(disable : 4204)
#    pragma warning(disable : 4706)
#endif

int aws_byte_buf_init(struct aws_byte_buf *buf, struct aws_allocator *allocator, size_t capacity) {
    AWS_PRECONDITION(buf);
    AWS_PRECONDITION(allocator);

    buf->buffer = (capacity == 0) ? NULL : aws_mem_acquire(allocator, capacity);
    if (capacity != 0 && buf->buffer == NULL) {
        return AWS_OP_ERR;
    }

    buf->len = 0;
    buf->capacity = capacity;
    buf->allocator = allocator;
    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_init_copy(struct aws_byte_buf *dest, struct aws_allocator *allocator, const struct aws_byte_buf *src) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(dest);
    AWS_ERROR_PRECONDITION(aws_byte_buf_is_valid(src));

    if (!src->buffer) {
        AWS_ZERO_STRUCT(*dest);
        dest->allocator = allocator;
        AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
        return AWS_OP_SUCCESS;
    }

    *dest = *src;
    dest->allocator = allocator;
    dest->buffer = (uint8_t *)aws_mem_acquire(allocator, src->capacity);
    if (dest->buffer == NULL) {
        AWS_ZERO_STRUCT(*dest);
        return AWS_OP_ERR;
    }
    memcpy(dest->buffer, src->buffer, src->len);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
    return AWS_OP_SUCCESS;
}

bool aws_byte_buf_is_valid(const struct aws_byte_buf *const buf) {
    return buf && ((buf->capacity == 0 && buf->len == 0 && buf->buffer == NULL) ||
                   (buf->capacity > 0 && buf->len <= buf->capacity && AWS_MEM_IS_WRITABLE(buf->buffer, buf->len)));
}

bool aws_byte_cursor_is_valid(const struct aws_byte_cursor *cursor) {
    return cursor &&
           ((cursor->len == 0) || (cursor->len > 0 && cursor->ptr && AWS_MEM_IS_READABLE(cursor->ptr, cursor->len)));
}

void aws_byte_buf_reset(struct aws_byte_buf *buf, bool zero_contents) {
    if (zero_contents) {
        aws_byte_buf_secure_zero(buf);
    }
    buf->len = 0;
}

void aws_byte_buf_clean_up(struct aws_byte_buf *buf) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    if (buf->allocator && buf->buffer) {
        aws_mem_release(buf->allocator, (void *)buf->buffer);
    }
    buf->allocator = NULL;
    buf->buffer = NULL;
    buf->len = 0;
    buf->capacity = 0;
}

void aws_byte_buf_secure_zero(struct aws_byte_buf *buf) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    if (buf->buffer) {
        aws_secure_zero(buf->buffer, buf->capacity);
    }
    buf->len = 0;
    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
}

void aws_byte_buf_clean_up_secure(struct aws_byte_buf *buf) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    aws_byte_buf_secure_zero(buf);
    aws_byte_buf_clean_up(buf);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
}

bool aws_byte_buf_eq(const struct aws_byte_buf *const a, const struct aws_byte_buf *const b) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(a));
    AWS_PRECONDITION(aws_byte_buf_is_valid(b));
    bool rval = aws_array_eq(a->buffer, a->len, b->buffer, b->len);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(a));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(b));
    return rval;
}

bool aws_byte_buf_eq_ignore_case(const struct aws_byte_buf *const a, const struct aws_byte_buf *const b) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(a));
    AWS_PRECONDITION(aws_byte_buf_is_valid(b));
    bool rval = aws_array_eq_ignore_case(a->buffer, a->len, b->buffer, b->len);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(a));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(b));
    return rval;
}

bool aws_byte_buf_eq_c_str(const struct aws_byte_buf *const buf, const char *const c_str) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(c_str != NULL);
    bool rval = aws_array_eq_c_str(buf->buffer, buf->len, c_str);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
    return rval;
}

bool aws_byte_buf_eq_c_str_ignore_case(const struct aws_byte_buf *const buf, const char *const c_str) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(c_str != NULL);
    bool rval = aws_array_eq_c_str_ignore_case(buf->buffer, buf->len, c_str);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
    return rval;
}

int aws_byte_buf_init_copy_from_cursor(
    struct aws_byte_buf *dest,
    struct aws_allocator *allocator,
    struct aws_byte_cursor src) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(dest);
    AWS_ERROR_PRECONDITION(aws_byte_cursor_is_valid(&src));

    AWS_ZERO_STRUCT(*dest);

    dest->buffer = (src.len > 0) ? (uint8_t *)aws_mem_acquire(allocator, src.len) : NULL;
    if (src.len != 0 && dest->buffer == NULL) {
        return AWS_OP_ERR;
    }

    dest->len = src.len;
    dest->capacity = src.len;
    dest->allocator = allocator;
    if (src.len > 0) {
        memcpy(dest->buffer, src.ptr, src.len);
    }
    AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
    return AWS_OP_SUCCESS;
}

bool aws_byte_cursor_next_split(
    const struct aws_byte_cursor *AWS_RESTRICT input_str,
    char split_on,
    struct aws_byte_cursor *AWS_RESTRICT substr) {

    bool first_run = false;
    if (!substr->ptr) {
        first_run = true;
        substr->ptr = input_str->ptr;
        substr->len = 0;
    }

    if (substr->ptr > input_str->ptr + input_str->len) {
        /* This will hit if the last substring returned was an empty string after terminating split_on. */
        AWS_ZERO_STRUCT(*substr);
        return false;
    }

    /* Calculate first byte to search. */
    substr->ptr += substr->len;
    /* Remaining bytes is the number we started with minus the number of bytes already read. */
    substr->len = input_str->len - (substr->ptr - input_str->ptr);

    if (!first_run && substr->len == 0) {
        /* This will hit if the string doesn't end with split_on but we're done. */
        AWS_ZERO_STRUCT(*substr);
        return false;
    }

    if (!first_run && *substr->ptr == split_on) {
        /* If not first rodeo and the character after substr is split_on, skip. */
        ++substr->ptr;
        --substr->len;

        if (substr->len == 0) {
            /* If split character was last in the string, return empty substr. */
            return true;
        }
    }

    uint8_t *new_location = memchr(substr->ptr, split_on, substr->len);
    if (new_location) {

        /* Character found, update string length. */
        substr->len = new_location - substr->ptr;
    }

    return true;
}

int aws_byte_cursor_split_on_char_n(
    const struct aws_byte_cursor *AWS_RESTRICT input_str,
    char split_on,
    size_t n,
    struct aws_array_list *AWS_RESTRICT output) {
    AWS_ASSERT(input_str && input_str->ptr);
    AWS_ASSERT(output);
    AWS_ASSERT(output->item_size >= sizeof(struct aws_byte_cursor));

    size_t max_splits = n > 0 ? n : SIZE_MAX;
    size_t split_count = 0;

    struct aws_byte_cursor substr;
    AWS_ZERO_STRUCT(substr);

    /* Until we run out of substrs or hit the max split count, keep iterating and pushing into the array list. */
    while (split_count <= max_splits && aws_byte_cursor_next_split(input_str, split_on, &substr)) {

        if (split_count == max_splits) {
            /* If this is the last split, take the rest of the string. */
            substr.len = input_str->len - (substr.ptr - input_str->ptr);
        }

        if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&substr))) {
            return AWS_OP_ERR;
        }
        ++split_count;
    }

    return AWS_OP_SUCCESS;
}

int aws_byte_cursor_split_on_char(
    const struct aws_byte_cursor *AWS_RESTRICT input_str,
    char split_on,
    struct aws_array_list *AWS_RESTRICT output) {

    return aws_byte_cursor_split_on_char_n(input_str, split_on, 0, output);
}

int aws_byte_buf_cat(struct aws_byte_buf *dest, size_t number_of_args, ...) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(dest));

    va_list ap;
    va_start(ap, number_of_args);

    for (size_t i = 0; i < number_of_args; ++i) {
        struct aws_byte_buf *buffer = va_arg(ap, struct aws_byte_buf *);
        struct aws_byte_cursor cursor = aws_byte_cursor_from_buf(buffer);

        if (aws_byte_buf_append(dest, &cursor)) {
            va_end(ap);
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_ERR;
        }
    }

    va_end(ap);
    AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
    return AWS_OP_SUCCESS;
}

bool aws_byte_cursor_eq(const struct aws_byte_cursor *a, const struct aws_byte_cursor *b) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(a));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(b));
    bool rv = aws_array_eq(a->ptr, a->len, b->ptr, b->len);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(a));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(b));
    return rv;
}

bool aws_byte_cursor_eq_ignore_case(const struct aws_byte_cursor *a, const struct aws_byte_cursor *b) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(a));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(b));
    bool rv = aws_array_eq_ignore_case(a->ptr, a->len, b->ptr, b->len);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(a));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(b));
    return rv;
}

/* Every possible uint8_t value, lowercased */
static const uint8_t s_tolower_table[256] = {
    0,   1,   2,   3,   4,   5,   6,   7,   8,   9,   10,  11,  12,  13,  14,  15,  16,  17,  18,  19,  20,  21,
    22,  23,  24,  25,  26,  27,  28,  29,  30,  31,  32,  33,  34,  35,  36,  37,  38,  39,  40,  41,  42,  43,
    44,  45,  46,  47,  48,  49,  50,  51,  52,  53,  54,  55,  56,  57,  58,  59,  60,  61,  62,  63,  64,  'a',
    'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w',
    'x', 'y', 'z', 91,  92,  93,  94,  95,  96,  'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
    'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 123, 124, 125, 126, 127, 128, 129, 130, 131,
    132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
    154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
    176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197,
    198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
    220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241,
    242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255};

const uint8_t *aws_lookup_table_to_lower_get(void) {
    return s_tolower_table;
}

bool aws_array_eq_ignore_case(
    const void *const array_a,
    const size_t len_a,
    const void *const array_b,
    const size_t len_b) {
    AWS_PRECONDITION(
        (len_a == 0) || AWS_MEM_IS_READABLE(array_a, len_a), "Input array [array_a] must be readable up to [len_a].");
    AWS_PRECONDITION(
        (len_b == 0) || AWS_MEM_IS_READABLE(array_b, len_b), "Input array [array_b] must be readable up to [len_b].");

    if (len_a != len_b) {
        return false;
    }

    const uint8_t *bytes_a = array_a;
    const uint8_t *bytes_b = array_b;
    for (size_t i = 0; i < len_a; ++i) {
        if (s_tolower_table[bytes_a[i]] != s_tolower_table[bytes_b[i]]) {
            return false;
        }
    }

    return true;
}

bool aws_array_eq(const void *const array_a, const size_t len_a, const void *const array_b, const size_t len_b) {
    AWS_PRECONDITION(
        (len_a == 0) || AWS_MEM_IS_READABLE(array_a, len_a), "Input array [array_a] must be readable up to [len_a].");
    AWS_PRECONDITION(
        (len_b == 0) || AWS_MEM_IS_READABLE(array_b, len_b), "Input array [array_b] must be readable up to [len_b].");

    if (len_a != len_b) {
        return false;
    }

    if (len_a == 0) {
        return true;
    }

    return !memcmp(array_a, array_b, len_a);
}

bool aws_array_eq_c_str_ignore_case(const void *const array, const size_t array_len, const char *const c_str) {
    AWS_PRECONDITION(
        array || (array_len == 0),
        "Either input pointer [array_a] mustn't be NULL or input [array_len] mustn't be zero.");
    AWS_PRECONDITION(c_str != NULL);

    /* Simpler implementation could have been:
     *   return aws_array_eq_ignore_case(array, array_len, c_str, strlen(c_str));
     * but that would have traversed c_str twice.
     * This implementation traverses c_str just once. */

    const uint8_t *array_bytes = array;
    const uint8_t *str_bytes = (const uint8_t *)c_str;

    for (size_t i = 0; i < array_len; ++i) {
        uint8_t s = str_bytes[i];
        if (s == '\0') {
            return false;
        }

        if (s_tolower_table[array_bytes[i]] != s_tolower_table[s]) {
            return false;
        }
    }

    return str_bytes[array_len] == '\0';
}

bool aws_array_eq_c_str(const void *const array, const size_t array_len, const char *const c_str) {
    AWS_PRECONDITION(
        array || (array_len == 0),
        "Either input pointer [array_a] mustn't be NULL or input [array_len] mustn't be zero.");
    AWS_PRECONDITION(c_str != NULL);

    /* Simpler implementation could have been:
     *   return aws_array_eq(array, array_len, c_str, strlen(c_str));
     * but that would have traversed c_str twice.
     * This implementation traverses c_str just once. */

    const uint8_t *array_bytes = array;
    const uint8_t *str_bytes = (const uint8_t *)c_str;

    for (size_t i = 0; i < array_len; ++i) {
        uint8_t s = str_bytes[i];
        if (s == '\0') {
            return false;
        }

        if (array_bytes[i] != s) {
            return false;
        }
    }

    return str_bytes[array_len] == '\0';
}

uint64_t aws_hash_array_ignore_case(const void *array, const size_t len) {
    AWS_PRECONDITION(AWS_MEM_IS_READABLE(array, len));
    /* FNV-1a: https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function */
    const uint64_t fnv_offset_basis = 0xcbf29ce484222325ULL;
    const uint64_t fnv_prime = 0x100000001b3ULL;

    const uint8_t *i = array;
    const uint8_t *end = i + len;

    uint64_t hash = fnv_offset_basis;
    while (i != end) {
        const uint8_t lower = s_tolower_table[*i++];
        hash ^= lower;
#ifdef CBMC
#    pragma CPROVER check push
#    pragma CPROVER check disable "unsigned-overflow"
#endif
        hash *= fnv_prime;
#ifdef CBMC
#    pragma CPROVER check pop
#endif
    }
    return hash;
}

uint64_t aws_hash_byte_cursor_ptr_ignore_case(const void *item) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(item));
    const struct aws_byte_cursor *const cursor = item;
    uint64_t rval = aws_hash_array_ignore_case(cursor->ptr, cursor->len);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(item));
    return rval;
}

bool aws_byte_cursor_eq_byte_buf(const struct aws_byte_cursor *const a, const struct aws_byte_buf *const b) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(a));
    AWS_PRECONDITION(aws_byte_buf_is_valid(b));
    bool rv = aws_array_eq(a->ptr, a->len, b->buffer, b->len);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(a));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(b));
    return rv;
}

bool aws_byte_cursor_eq_byte_buf_ignore_case(
    const struct aws_byte_cursor *const a,
    const struct aws_byte_buf *const b) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(a));
    AWS_PRECONDITION(aws_byte_buf_is_valid(b));
    bool rv = aws_array_eq_ignore_case(a->ptr, a->len, b->buffer, b->len);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(a));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(b));
    return rv;
}

bool aws_byte_cursor_eq_c_str(const struct aws_byte_cursor *const cursor, const char *const c_str) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cursor));
    AWS_PRECONDITION(c_str != NULL);
    bool rv = aws_array_eq_c_str(cursor->ptr, cursor->len, c_str);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cursor));
    return rv;
}

bool aws_byte_cursor_eq_c_str_ignore_case(const struct aws_byte_cursor *const cursor, const char *const c_str) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cursor));
    AWS_PRECONDITION(c_str != NULL);
    bool rv = aws_array_eq_c_str_ignore_case(cursor->ptr, cursor->len, c_str);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cursor));
    return rv;
}

int aws_byte_buf_append(struct aws_byte_buf *to, const struct aws_byte_cursor *from) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(to));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(from));

    if (to->capacity - to->len < from->len) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
        AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }

    if (from->len > 0) {
        /* This assert teaches clang-tidy that from->ptr and to->buffer cannot be null in a non-empty buffers */
        AWS_ASSERT(from->ptr);
        AWS_ASSERT(to->buffer);
        memcpy(to->buffer + to->len, from->ptr, from->len);
        to->len += from->len;
    }

    AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_append_with_lookup(
    struct aws_byte_buf *AWS_RESTRICT to,
    const struct aws_byte_cursor *AWS_RESTRICT from,
    const uint8_t *lookup_table) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(to));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(from));
    AWS_PRECONDITION(
        AWS_MEM_IS_READABLE(lookup_table, 256), "Input array [lookup_table] must be at least 256 bytes long.");

    if (to->capacity - to->len < from->len) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
        AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }

    for (size_t i = 0; i < from->len; ++i) {
        to->buffer[to->len + i] = lookup_table[from->ptr[i]];
    }

    if (aws_add_size_checked(to->len, from->len, &to->len)) {
        return AWS_OP_ERR;
    }

    AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_append_dynamic(struct aws_byte_buf *to, const struct aws_byte_cursor *from) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(to));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(from));
    AWS_ERROR_PRECONDITION(to->allocator);

    if (to->capacity - to->len < from->len) {
        /*
         * NewCapacity = Max(OldCapacity * 2, OldCapacity + MissingCapacity)
         */
        size_t missing_capacity = from->len - (to->capacity - to->len);

        size_t required_capacity = 0;
        if (aws_add_size_checked(to->capacity, missing_capacity, &required_capacity)) {
            AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
            AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
            return AWS_OP_ERR;
        }

        /*
         * It's ok if this overflows, just clamp to max possible.
         * In theory this lets us still grow a buffer that's larger than 1/2 size_t space
         * at least enough to accommodate the append.
         */
        size_t growth_capacity = aws_add_size_saturating(to->capacity, to->capacity);

        size_t new_capacity = required_capacity;
        if (new_capacity < growth_capacity) {
            new_capacity = growth_capacity;
        }

        /*
         * Attempt to resize - we intentionally do not use reserve() in order to preserve
         * the (unlikely) use case of from and to being the same buffer range.
         */

        /*
         * Try the max, but if that fails and the required is smaller, try it in fallback
         */
        uint8_t *new_buffer = aws_mem_acquire(to->allocator, new_capacity);
        if (new_buffer == NULL) {
            if (new_capacity > required_capacity) {
                new_capacity = required_capacity;
                new_buffer = aws_mem_acquire(to->allocator, new_capacity);
                if (new_buffer == NULL) {
                    AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
                    AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
                    return AWS_OP_ERR;
                }
            } else {
                AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
                AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
                return AWS_OP_ERR;
            }
        }

        /*
         * Copy old buffer -> new buffer
         */
        if (to->len > 0) {
            memcpy(new_buffer, to->buffer, to->len);
        }
        /*
         * Copy what we actually wanted to append in the first place
         */
        if (from->len > 0) {
            memcpy(new_buffer + to->len, from->ptr, from->len);
        }
        /*
         * Get rid of the old buffer
         */
        aws_mem_release(to->allocator, to->buffer);

        /*
         * Switch to the new buffer
         */
        to->buffer = new_buffer;
        to->capacity = new_capacity;
    } else {
        if (from->len > 0) {
            /* This assert teaches clang-tidy that from->ptr and to->buffer cannot be null in a non-empty buffers */
            AWS_ASSERT(from->ptr);
            AWS_ASSERT(to->buffer);
            memcpy(to->buffer + to->len, from->ptr, from->len);
        }
    }

    to->len += from->len;

    AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_reserve(struct aws_byte_buf *buffer, size_t requested_capacity) {
    AWS_ERROR_PRECONDITION(buffer->allocator);
    AWS_ERROR_PRECONDITION(aws_byte_buf_is_valid(buffer));

    if (requested_capacity <= buffer->capacity) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
        return AWS_OP_SUCCESS;
    }

    if (aws_mem_realloc(buffer->allocator, (void **)&buffer->buffer, buffer->capacity, requested_capacity)) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
        return AWS_OP_ERR;
    }

    buffer->capacity = requested_capacity;

    AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_reserve_relative(struct aws_byte_buf *buffer, size_t additional_length) {
    AWS_ERROR_PRECONDITION(buffer->allocator);
    AWS_ERROR_PRECONDITION(aws_byte_buf_is_valid(buffer));

    size_t requested_capacity = 0;
    if (AWS_UNLIKELY(aws_add_size_checked(buffer->len, additional_length, &requested_capacity))) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
        return AWS_OP_ERR;
    }

    return aws_byte_buf_reserve(buffer, requested_capacity);
}

struct aws_byte_cursor aws_byte_cursor_right_trim_pred(
    const struct aws_byte_cursor *source,
    aws_byte_predicate_fn *predicate) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(source));
    AWS_PRECONDITION(predicate != NULL);
    struct aws_byte_cursor trimmed = *source;

    while (trimmed.len > 0 && predicate(*(trimmed.ptr + trimmed.len - 1))) {
        --trimmed.len;
    }
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(source));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&trimmed));
    return trimmed;
}

struct aws_byte_cursor aws_byte_cursor_left_trim_pred(
    const struct aws_byte_cursor *source,
    aws_byte_predicate_fn *predicate) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(source));
    AWS_PRECONDITION(predicate != NULL);
    struct aws_byte_cursor trimmed = *source;

    while (trimmed.len > 0 && predicate(*(trimmed.ptr))) {
        --trimmed.len;
        ++trimmed.ptr;
    }
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(source));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&trimmed));
    return trimmed;
}

struct aws_byte_cursor aws_byte_cursor_trim_pred(
    const struct aws_byte_cursor *source,
    aws_byte_predicate_fn *predicate) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(source));
    AWS_PRECONDITION(predicate != NULL);
    struct aws_byte_cursor left_trimmed = aws_byte_cursor_left_trim_pred(source, predicate);
    struct aws_byte_cursor dest = aws_byte_cursor_right_trim_pred(&left_trimmed, predicate);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(source));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&dest));
    return dest;
}

bool aws_byte_cursor_satisfies_pred(const struct aws_byte_cursor *source, aws_byte_predicate_fn *predicate) {
    struct aws_byte_cursor trimmed = aws_byte_cursor_left_trim_pred(source, predicate);
    bool rval = (trimmed.len == 0);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(source));
    return rval;
}

int aws_byte_cursor_compare_lexical(const struct aws_byte_cursor *lhs, const struct aws_byte_cursor *rhs) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(lhs));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(rhs));
    /* make sure we don't pass NULL pointers to memcmp */
    AWS_PRECONDITION(lhs->ptr != NULL);
    AWS_PRECONDITION(rhs->ptr != NULL);
    size_t comparison_length = lhs->len;
    if (comparison_length > rhs->len) {
        comparison_length = rhs->len;
    }

    int result = memcmp(lhs->ptr, rhs->ptr, comparison_length);

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(lhs));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(rhs));
    if (result != 0) {
        return result;
    }

    if (lhs->len != rhs->len) {
        return comparison_length == lhs->len ? -1 : 1;
    }

    return 0;
}

int aws_byte_cursor_compare_lookup(
    const struct aws_byte_cursor *lhs,
    const struct aws_byte_cursor *rhs,
    const uint8_t *lookup_table) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(lhs));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(rhs));
    AWS_PRECONDITION(AWS_MEM_IS_READABLE(lookup_table, 256));
    const uint8_t *lhs_curr = lhs->ptr;
    const uint8_t *lhs_end = lhs_curr + lhs->len;

    const uint8_t *rhs_curr = rhs->ptr;
    const uint8_t *rhs_end = rhs_curr + rhs->len;

    while (lhs_curr < lhs_end && rhs_curr < rhs_end) {
        uint8_t lhc = lookup_table[*lhs_curr];
        uint8_t rhc = lookup_table[*rhs_curr];

        AWS_POSTCONDITION(aws_byte_cursor_is_valid(lhs));
        AWS_POSTCONDITION(aws_byte_cursor_is_valid(rhs));
        if (lhc < rhc) {
            return -1;
        }

        if (lhc > rhc) {
            return 1;
        }

        lhs_curr++;
        rhs_curr++;
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(lhs));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(rhs));
    if (lhs_curr < lhs_end) {
        return 1;
    }

    if (rhs_curr < rhs_end) {
        return -1;
    }

    return 0;
}

/**
 * For creating a byte buffer from a null-terminated string literal.
 */
struct aws_byte_buf aws_byte_buf_from_c_str(const char *c_str) {
    struct aws_byte_buf buf;
    buf.len = (!c_str) ? 0 : strlen(c_str);
    buf.capacity = buf.len;
    buf.buffer = (buf.capacity == 0) ? NULL : (uint8_t *)c_str;
    buf.allocator = NULL;
    AWS_POSTCONDITION(aws_byte_buf_is_valid(&buf));
    return buf;
}

struct aws_byte_buf aws_byte_buf_from_array(const void *bytes, size_t len) {
    AWS_PRECONDITION(AWS_MEM_IS_WRITABLE(bytes, len), "Input array [bytes] must be writable up to [len] bytes.");
    struct aws_byte_buf buf;
    buf.buffer = (len > 0) ? (uint8_t *)bytes : NULL;
    buf.len = len;
    buf.capacity = len;
    buf.allocator = NULL;
    AWS_POSTCONDITION(aws_byte_buf_is_valid(&buf));
    return buf;
}

struct aws_byte_buf aws_byte_buf_from_empty_array(const void *bytes, size_t capacity) {
    AWS_PRECONDITION(
        AWS_MEM_IS_WRITABLE(bytes, capacity), "Input array [bytes] must be writable up to [capacity] bytes.");
    struct aws_byte_buf buf;
    buf.buffer = (capacity > 0) ? (uint8_t *)bytes : NULL;
    buf.len = 0;
    buf.capacity = capacity;
    buf.allocator = NULL;
    AWS_POSTCONDITION(aws_byte_buf_is_valid(&buf));
    return buf;
}

struct aws_byte_cursor aws_byte_cursor_from_buf(const struct aws_byte_buf *const buf) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    struct aws_byte_cursor cur;
    cur.ptr = buf->buffer;
    cur.len = buf->len;
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&cur));
    return cur;
}

struct aws_byte_cursor aws_byte_cursor_from_c_str(const char *c_str) {
    struct aws_byte_cursor cur;
    cur.ptr = (uint8_t *)c_str;
    cur.len = (cur.ptr) ? strlen(c_str) : 0;
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&cur));
    return cur;
}

struct aws_byte_cursor aws_byte_cursor_from_array(const void *const bytes, const size_t len) {
    AWS_PRECONDITION(len == 0 || AWS_MEM_IS_READABLE(bytes, len), "Input array [bytes] must be readable up to [len].");
    struct aws_byte_cursor cur;
    cur.ptr = (uint8_t *)bytes;
    cur.len = len;
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&cur));
    return cur;
}

#ifdef CBMC
#    pragma CPROVER check push
#    pragma CPROVER check disable "unsigned-overflow"
#endif
/**
 * If index >= bound, bound > (SIZE_MAX / 2), or index > (SIZE_MAX / 2), returns
 * 0. Otherwise, returns UINTPTR_MAX.  This function is designed to return the correct
 * value even under CPU speculation conditions, and is intended to be used for
 * SPECTRE mitigation purposes.
 */
size_t aws_nospec_mask(size_t index, size_t bound) {
    /*
     * SPECTRE mitigation - we compute a mask that will be zero if len < 0
     * or len >= buf->len, and all-ones otherwise, and AND it into the index.
     * It is critical that we avoid any branches in this logic.
     */

    /*
     * Hide the index value from the optimizer. This helps ensure that all this
     * logic doesn't get eliminated.
     */
#if defined(__GNUC__) || defined(__clang__)
    __asm__ __volatile__("" : "+r"(index));
#endif
#if defined(_MSVC_LANG)
    /*
     * MSVC doesn't have a good way for us to blind the optimizer, and doesn't
     * even have inline asm on x64. Some experimentation indicates that this
     * hack seems to confuse it sufficiently for our needs.
     */
    *((volatile uint8_t *)&index) += 0;
#endif

    /*
     * If len > (SIZE_MAX / 2), then we can end up with len - buf->len being
     * positive simply because the sign bit got inverted away. So we also check
     * that the sign bit isn't set from the start.
     *
     * We also check that bound <= (SIZE_MAX / 2) to catch cases where the
     * buffer is _already_ out of bounds.
     */
    size_t negative_mask = index | bound;
    size_t toobig_mask = bound - index - (uintptr_t)1;
    size_t combined_mask = negative_mask | toobig_mask;

    /*
     * combined_mask needs to have its sign bit OFF for us to be in range.
     * We'd like to expand this to a mask we can AND into our index, so flip
     * that bit (and everything else), shift it over so it's the only bit in the
     * ones position, and multiply across the entire register.
     *
     * First, extract the (inverse) top bit and move it to the lowest bit.
     * Because there's no standard SIZE_BIT in C99, we'll divide by a mask with
     * just the top bit set instead.
     */

    combined_mask = (~combined_mask) / (SIZE_MAX - (SIZE_MAX >> 1));

    /*
     * Now multiply it to replicate it across all bits.
     *
     * Note that GCC is smart enough to optimize the divide-and-multiply into
     * an arithmetic right shift operation on x86.
     */
    combined_mask = combined_mask * UINTPTR_MAX;

    return combined_mask;
}
#ifdef CBMC
#    pragma CPROVER check pop
#endif

/**
 * Tests if the given aws_byte_cursor has at least len bytes remaining. If so,
 * *buf is advanced by len bytes (incrementing ->ptr and decrementing ->len),
 * and an aws_byte_cursor referring to the first len bytes of the original *buf
 * is returned. Otherwise, an aws_byte_cursor with ->ptr = NULL, ->len = 0 is
 * returned.
 *
 * Note that if len is above (SIZE_MAX / 2), this function will also treat it as
 * a buffer overflow, and return NULL without changing *buf.
 */
struct aws_byte_cursor aws_byte_cursor_advance(struct aws_byte_cursor *const cursor, const size_t len) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cursor));
    struct aws_byte_cursor rv;
    if (cursor->len > (SIZE_MAX >> 1) || len > (SIZE_MAX >> 1) || len > cursor->len) {
        rv.ptr = NULL;
        rv.len = 0;
    } else {
        rv.ptr = cursor->ptr;
        rv.len = len;

        cursor->ptr += len;
        cursor->len -= len;
    }
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cursor));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&rv));
    return rv;
}

/**
 * Behaves identically to aws_byte_cursor_advance, but avoids speculative
 * execution potentially reading out-of-bounds pointers (by returning an
 * empty ptr in such speculated paths).
 *
 * This should generally be done when using an untrusted or
 * data-dependent value for 'len', to avoid speculating into a path where
 * cursor->ptr points outside the true ptr length.
 */

struct aws_byte_cursor aws_byte_cursor_advance_nospec(struct aws_byte_cursor *const cursor, size_t len) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cursor));

    struct aws_byte_cursor rv;

    if (len <= cursor->len && len <= (SIZE_MAX >> 1) && cursor->len <= (SIZE_MAX >> 1)) {
        /*
         * If we're speculating past a failed bounds check, null out the pointer. This ensures
         * that we don't try to read past the end of the buffer and leak information about other
         * memory through timing side-channels.
         */
        uintptr_t mask = aws_nospec_mask(len, cursor->len + 1);

        /* Make sure we don't speculate-underflow len either */
        len = len & mask;
        cursor->ptr = (uint8_t *)((uintptr_t)cursor->ptr & mask);
        /* Make sure subsequent nospec accesses don't advance ptr past NULL */
        cursor->len = cursor->len & mask;

        rv.ptr = cursor->ptr;
        /* Make sure anything acting upon the returned cursor _also_ doesn't advance past NULL */
        rv.len = len & mask;

        cursor->ptr += len;
        cursor->len -= len;
    } else {
        rv.ptr = NULL;
        rv.len = 0;
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cursor));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(&rv));
    return rv;
}

/**
 * Reads specified length of data from byte cursor and copies it to the
 * destination array.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read(struct aws_byte_cursor *AWS_RESTRICT cur, void *AWS_RESTRICT dest, const size_t len) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(AWS_MEM_IS_WRITABLE(dest, len));
    struct aws_byte_cursor slice = aws_byte_cursor_advance_nospec(cur, len);

    if (slice.ptr) {
        memcpy(dest, slice.ptr, len);
        AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
        AWS_POSTCONDITION(AWS_MEM_IS_READABLE(dest, len));
        return true;
    }
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return false;
}

/**
 * Reads as many bytes from cursor as size of buffer, and copies them to buffer.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_and_fill_buffer(
    struct aws_byte_cursor *AWS_RESTRICT cur,
    struct aws_byte_buf *AWS_RESTRICT dest) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(aws_byte_buf_is_valid(dest));
    if (aws_byte_cursor_read(cur, dest->buffer, dest->capacity)) {
        dest->len = dest->capacity;
        AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
        return true;
    }
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
    return false;
}

/**
 * Reads a single byte from cursor, placing it in *var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_u8(struct aws_byte_cursor *AWS_RESTRICT cur, uint8_t *AWS_RESTRICT var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    bool rv = aws_byte_cursor_read(cur, var, 1);
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return rv;
}

/**
 * Reads a 16-bit value in network byte order from cur, and places it in host
 * byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_be16(struct aws_byte_cursor *cur, uint16_t *var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(var));
    bool rv = aws_byte_cursor_read(cur, var, 2);

    if (AWS_LIKELY(rv)) {
        *var = aws_ntoh16(*var);
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return rv;
}

/**
 * Reads a 32-bit value in network byte order from cur, and places it in host
 * byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_be32(struct aws_byte_cursor *cur, uint32_t *var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(var));
    bool rv = aws_byte_cursor_read(cur, var, 4);

    if (AWS_LIKELY(rv)) {
        *var = aws_ntoh32(*var);
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return rv;
}

/**
 * Reads a 32-bit value in network byte order from cur, and places it in host
 * byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_float_be32(struct aws_byte_cursor *cur, float *var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(var));
    bool rv = aws_byte_cursor_read(cur, var, sizeof(float));

    if (AWS_LIKELY(rv)) {
        *var = aws_ntohf32(*var);
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return rv;
}

/**
 * Reads a 64-bit value in network byte order from cur, and places it in host
 * byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_float_be64(struct aws_byte_cursor *cur, double *var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(var));
    bool rv = aws_byte_cursor_read(cur, var, sizeof(double));

    if (AWS_LIKELY(rv)) {
        *var = aws_ntohf64(*var);
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return rv;
}

/**
 * Reads a 64-bit value in network byte order from cur, and places it in host
 * byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_cursor_read_be64(struct aws_byte_cursor *cur, uint64_t *var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cur));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(var));
    bool rv = aws_byte_cursor_read(cur, var, sizeof(*var));

    if (AWS_LIKELY(rv)) {
        *var = aws_ntoh64(*var);
    }

    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cur));
    return rv;
}

/**
 * Appends a sub-buffer to the specified buffer.
 *
 * If the buffer has at least `len' bytes remaining (buffer->capacity - buffer->len >= len),
 * then buffer->len is incremented by len, and an aws_byte_buf is assigned to *output corresponding
 * to the last len bytes of the input buffer. The aws_byte_buf at *output will have a null
 * allocator, a zero initial length, and a capacity of 'len'. The function then returns true.
 *
 * If there is insufficient space, then this function nulls all fields in *output and returns
 * false.
 */
bool aws_byte_buf_advance(
    struct aws_byte_buf *const AWS_RESTRICT buffer,
    struct aws_byte_buf *const AWS_RESTRICT output,
    const size_t len) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buffer));
    AWS_PRECONDITION(aws_byte_buf_is_valid(output));
    if (buffer->capacity - buffer->len >= len) {
        *output = aws_byte_buf_from_array(buffer->buffer + buffer->len, len);
        buffer->len += len;
        output->len = 0;
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(output));
        return true;
    } else {
        AWS_ZERO_STRUCT(*output);
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(output));
        return false;
    }
}

/**
 * Write specified number of bytes from array to byte buffer.
 *
 * On success, returns true and updates the buffer length accordingly.
 * If there is insufficient space in the buffer, returns false, leaving the
 * buffer unchanged.
 */
bool aws_byte_buf_write(struct aws_byte_buf *AWS_RESTRICT buf, const uint8_t *AWS_RESTRICT src, size_t len) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(AWS_MEM_IS_WRITABLE(src, len), "Input array [src] must be readable up to [len] bytes.");

    if (buf->len > (SIZE_MAX >> 1) || len > (SIZE_MAX >> 1) || buf->len + len > buf->capacity) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
        return false;
    }

    memcpy(buf->buffer + buf->len, src, len);
    buf->len += len;

    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
    return true;
}

/**
 * Copies all bytes from buffer to buffer.
 *
 * On success, returns true and updates the buffer /length accordingly.
 * If there is insufficient space in the buffer, returns false, leaving the
 * buffer unchanged.
 */
bool aws_byte_buf_write_from_whole_buffer(struct aws_byte_buf *AWS_RESTRICT buf, struct aws_byte_buf src) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(aws_byte_buf_is_valid(&src));
    return aws_byte_buf_write(buf, src.buffer, src.len);
}

/**
 * Copies all bytes from buffer to buffer.
 *
 * On success, returns true and updates the buffer /length accordingly.
 * If there is insufficient space in the buffer, returns false, leaving the
 * buffer unchanged.
 */
bool aws_byte_buf_write_from_whole_cursor(struct aws_byte_buf *AWS_RESTRICT buf, struct aws_byte_cursor src) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&src));
    return aws_byte_buf_write(buf, src.ptr, src.len);
}

/**
 * Copies one byte to buffer.
 *
 * On success, returns true and updates the cursor /length
 accordingly.

 * If there is insufficient space in the cursor, returns false, leaving the
 cursor unchanged.
 */
bool aws_byte_buf_write_u8(struct aws_byte_buf *AWS_RESTRICT buf, uint8_t c) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    return aws_byte_buf_write(buf, &c, 1);
}

/**
 * Writes a 16-bit integer in network byte order (big endian) to buffer.
 *
 * On success, returns true and updates the cursor /length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_buf_write_be16(struct aws_byte_buf *buf, uint16_t x) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    x = aws_hton16(x);
    return aws_byte_buf_write(buf, (uint8_t *)&x, 2);
}

/**
 * Writes a 32-bit integer in network byte order (big endian) to buffer.
 *
 * On success, returns true and updates the cursor /length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_buf_write_be32(struct aws_byte_buf *buf, uint32_t x) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    x = aws_hton32(x);
    return aws_byte_buf_write(buf, (uint8_t *)&x, 4);
}

/**
 * Writes a 32-bit float in network byte order (big endian) to buffer.
 *
 * On success, returns true and updates the cursor /length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_buf_write_float_be32(struct aws_byte_buf *buf, float x) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    x = aws_htonf32(x);
    return aws_byte_buf_write(buf, (uint8_t *)&x, 4);
}

/**
 * Writes a 64-bit integer in network byte order (big endian) to buffer.
 *
 * On success, returns true and updates the cursor /length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_buf_write_be64(struct aws_byte_buf *buf, uint64_t x) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    x = aws_hton64(x);
    return aws_byte_buf_write(buf, (uint8_t *)&x, 8);
}

/**
 * Writes a 64-bit float in network byte order (big endian) to buffer.
 *
 * On success, returns true and updates the cursor /length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the
 * cursor unchanged.
 */
bool aws_byte_buf_write_float_be64(struct aws_byte_buf *buf, double x) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    x = aws_htonf64(x);
    return aws_byte_buf_write(buf, (uint8_t *)&x, 8);
}
