declare ptr @malloc(i64)

%Data.A = type { i32 } ; a
%Data.B = type { ptr, i32, i32, i32 } ; Data.A, b, c, d
%Data.C = type { ptr, i32 } ; Data.A, c
%Data.D = type { ptr, ptr, ptr } ; Data.B, Data.A, Data.C


define ptr @__global__Data.test3() {
	%size_0 = ptrtoint %Data.B* getelementptr (%Data.B, %Data.B* null, i32 1) to i64
	%ptr_Data.B_0 = call ptr @malloc(i64 %size_0)
	%size_1 = ptrtoint %Data.C* getelementptr (%Data.C, %Data.C* null, i32 1) to i64
	%ptr_Data.C_0 = call ptr @malloc(i64 %size_1)
	%size_2 = ptrtoint %Data.A* getelementptr (%Data.A, %Data.A* null, i32 1) to i64
	%ptr_Data.A_0 = call ptr @malloc(i64 %size_2)
	%size_3 = ptrtoint %Data.D* getelementptr (%Data.D, %Data.D* null, i32 1) to i64
	%ptr_Data.D_0 = call ptr @malloc(i64 %size_3)
	; Assign fields
	%v_0 = add i32 3, 5
	%ptr_Data.A_field_index0_0 = getelementptr %Data.A, ptr %ptr_Data.A_0, i32 0, i32 0
	store i32 %v_0, ptr %ptr_Data.A_field_index0_0
	%ptr_Data.B_field_index3_0 = getelementptr %Data.B, ptr %ptr_Data.B_0, i32 0, i32 3
	store i32 5, ptr %ptr_Data.B_field_index3_0
	%ptr_Data.B_field_index1_0 = getelementptr %Data.B, ptr %ptr_Data.B_0, i32 0, i32 1
	store i32 2, ptr %ptr_Data.B_field_index1_0
	%ptr_Data.B_field_index2_0 = getelementptr %Data.B, ptr %ptr_Data.B_0, i32 0, i32 2
	store i32 3, ptr %ptr_Data.B_field_index2_0
	; Assign parent pointers
	%ptr_Data.B_field_index0_0 = getelementptr %Data.B, ptr %ptr_Data.B_0, i32 0, i32 0
	store ptr %ptr_Data.A_0, ptr %ptr_Data.B_field_index0_0
	%ptr_Data.C_field_index0_0 = getelementptr %Data.C, ptr %ptr_Data.C_0, i32 0, i32 0
	store ptr %ptr_Data.A_0, ptr %ptr_Data.C_field_index0_0
	%ptr_Data.D_field_index0_0 = getelementptr %Data.D, ptr %ptr_Data.D_0, i32 0, i32 0
	store ptr %ptr_Data.B_0, ptr %ptr_Data.D_field_index0_0
	%ptr_Data.D_field_index2_0 = getelementptr %Data.D, ptr %ptr_Data.D_0, i32 0, i32 2
	store ptr %ptr_Data.C_0, ptr %ptr_Data.D_field_index2_0
	%ptr_Data.D_field_index1_0 = getelementptr %Data.D, ptr %ptr_Data.D_0, i32 0, i32 1
	store ptr %ptr_Data.A_0, ptr %ptr_Data.D_field_index1_0
	ret ptr %ptr_Data.D_0
}

define i32 @main() {
	%v_1 = call ptr @__global__Data.test3()
	%ptr_ptr_Data.B_0 = getelementptr %Data.D, ptr %v_1, i32 0, i32 0
	%ptr_Data.B_1 = load ptr, ptr %ptr_ptr_Data.B_0
	%ptr_field_index_0 = getelementptr %Data.B, ptr %ptr_Data.B_1, i32 0, i32 2
	%v_2 = load i32, ptr %ptr_field_index_0
	ret i32 %v_2
}