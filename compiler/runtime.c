#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static _Noreturn void runtime_fail(const char *format, ...) {
    va_list args;
    va_start(args, format);
    fputs("UPL runtime: ", stderr);
    vfprintf(stderr, format, args);
    va_end(args);
    fputc('\n', stderr);
    fflush(stderr);
    abort();
}

typedef struct {
    char *name;
    void* value;
} TheoryField;

typedef struct {
    TheoryField* fields;
    size_t field_count;
} Theory;

int compare_fields(const void *a, const void *b) {
    return strcmp(((TheoryField *)a)->name, ((TheoryField *)b)->name);
}

void* theory_create(size_t count, char *names[]) {
    Theory *theory = malloc(sizeof *theory);
    TheoryField *fields = calloc(count, sizeof *fields);
    if (!theory || !fields) {
        runtime_fail("Failed to allocate memory for theory");
    }
    theory->fields = fields;
    theory->field_count = count;
    for (size_t i = 0; i < count; i++) {
        theory->fields[i].name = names[i];
    }

    qsort(theory->fields, theory->field_count, sizeof(TheoryField), compare_fields);
    return theory;
}

TheoryField* theory_find_field(Theory *theory, char *name) {
    TheoryField target = {.name = name};
    TheoryField *result = bsearch(&target, theory->fields, theory->field_count, sizeof(TheoryField), compare_fields);
    if (!result) {
        runtime_fail("Failed to find field '%s'", name);
    }
    return result;
}

void theory_init_field(Theory *theory, char *name, void *value) {
    TheoryField *field = theory_find_field(theory, name);
    if (field->value) {
        runtime_fail("Tried to initialize already initialized field '%s'", name);
    }
    field->value = value;
}

void* theory_get_field(Theory *theory, char *name) {
    TheoryField *field = theory_find_field(theory, name);
    if (!field->value) {
        runtime_fail("Tried to access uninitialized field '%s'", name);
    }
    return field->value;
}
