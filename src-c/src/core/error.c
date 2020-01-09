#include "core/error.h"
#include "AST/ast.h"

#include <stdarg.h>
#include <stdio.h>

extern long line_positions[];
extern FILE *yyin;
extern bool hasError;

static const uint32_t kIndentionWidth = 4;

void logSemanticError(const Location *location, const char *format, ...) {
    hasError = true;
    fprintf(stderr, "<Error> Found in line %u, column %u: ", location->line,
            location->col);

    va_list args;
    va_start(args, format);
    vfprintf(stderr, format, args);
    va_end(args);

    if (fseek(yyin, line_positions[location->line], SEEK_SET) == 0) {
        char buffer[512];
        fgets(buffer, sizeof(buffer), yyin);
        fprintf(stderr, "\n%*s%s", kIndentionWidth, "", buffer);
        fprintf(stderr, "%*s\n", kIndentionWidth + location->col, "^");
    } else {
        fprintf(stderr, "Fail to reposition the yyin file stream.\n");
    }
}
