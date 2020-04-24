/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef STRING_H
#define STRING_H

/*!
 * \file string manipulation functions
 *
 * This API implement a subset of the POSIX string API,
 * with as much as possible respect for the standard
 * libstring definition as  defined in POSIX-1-2001, C09, C99,
 * SVr4 and 4.3BSD.
 */

#include "libc/types.h"
#include "lib_frama/__fc_string_axiomatic.h"

/*****************************************
 *  error handling helpers
 ****************************************/

/*
 * Not fully POSIX compliant (as no errno support) implementation of
 * strerror for syscalls return values
 */
const char *strerror(uint8_t ret);

/*****************************************
 * string manipulation functions
 *****************************************/

/*
 * Calculate the length of a NULL-terminated string.
 *
 * The length is equal to the effective number of characters, not
 * including the '\0' terminal one.
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */

/*@ requires valid_string_s: valid_read_string(s);
  @ assigns \result \from indirect:s[0..];
  @ ensures acsl_c_equiv: \result == strlen(s);
  @*/
uint32_t  strlen(const char * s);

/*
 * Compare two strings
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
int       strcmp(const char * s1,
                 const char * s2);

/*
 * Compare n first bytes of two strings
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
int       strncmp(const char *s1,
                  const char *s2,
                  uint32_t    n);


/*
 * Copy content from one string to another
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * WARNING: the length of dest *MUST* be known as greater than src lenght.
 * This function does *not* handle bound checking as it is not standard conform.
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
char *    strcpy(char *       dest,
                 const char * src);
/*
 * Copy n first bytes from one string to another
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
char *    strncpy(char *      dest,
                  const char *src,
                  uint32_t    n);

/*****************************************
 * memory bytes-based manipulation function
 *****************************************/

/*
 * Copy n bytes from one memory area to another
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Beware that there is no bound checking in byte-based memory manipulation
 * functions.
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
void *    memcpy(void *        dest,
                 const void *  src,
                 uint32_t      n);

/*
 * Compare n first bytes of two memory areas
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */
int       memcmp(const void *  s1,
                 const void *  s2,
                 int           n);
/*
 * Set n first bytes of a given memory area with a given byte value
 *
 * INFO: The C standard says that null argument(s) to string
 * functions produce undefined behavior.
 *
 * This is a global warning for the POSIX and C99/C99 libstring:
 * check your arguments before using it!
 *
 * Conforming to:
 * POSIX.1-2001, POSIX.1-2008, C89, C99, SVr4, 4.3BSD.
 */

void *    memset(void *        s,
                 int           c,
                 uint32_t      n);

#endif
