#include <stddef.h>

struct theory_field_entry {
    void* field_name_ptr;
    void* field_value_ptr;
    struct theory_field_entry* next_field_ptr;
};

void* theory_find_field(
    struct theory_field_entry* entry,
    void* field_name_ptr
) {
    while (entry != NULL) {
        if (entry->field_name_ptr == field_name_ptr) {
            return entry->field_value_ptr;
        }

        entry = entry->next_field_ptr;
    }

    return NULL;
}