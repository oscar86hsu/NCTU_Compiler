#ifndef __ERROR_H
#define __ERROR_H

/*
 * Check dies if Condition is not true
 */
#define CHECK(Condition, ErrorMsg)                                             \
    do {                                                                       \
        if (!(Condition)) {                                                    \
            fprintf(stderr, ErrorMsg);                                         \
            exit(-1);                                                          \
        }                                                                      \
    } while (0)

struct __Location;

void logSemanticError(const struct __Location *location, const char *format,
                      ...);

#endif
