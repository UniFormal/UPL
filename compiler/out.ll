declare ptr @malloc(i64)

%Data.T1_vtable = type { ptr, ptr }
%Data.T1 = type { %Data.T1_vtable* }
%Data.T2_vtable = type { ptr }
%Data.T2 = type { %Data.T2_vtable* }
%Data.T3_vtable = type { ptr, ptr, ptr, ptr }
%Data.T3 = type { %Data.T3_vtable*, %Data.T1_vtable*, %Data.T2_vtable* }
%Data.T4_vtable = type { ptr, ptr, ptr, ptr, ptr, ptr }
%Data.T4 = type { %Data.T4_vtable*, %Data.T1_vtable*, %Data.T3_vtable*, %Data.T2_vtable* }


define i32 @Data.T1.y() {
	ret i32 0
}

define i32 @Data.T1.x() {
	%v0 = add i32 3, 66
	ret i32 %v0
}

define i32 @Data.T2.x() {
	ret i32 0
}

define i32 @Data.T3.x() {
	%v1 = add i32 3, 66
	ret i32 %v1
}

define i32 @Data.T3.y() {
	ret i32 65
}

define i32 @Data.T3.z() {
	ret i32 5
}

define i32 @Data.T3.s() {
	ret i32 0
}

define i32 @Data.T4.x() {
	%v2 = add i32 3, 66
	ret i32 %v2
}

define i32 @Data.T4.y() {
	ret i32 65
}

define i32 @Data.T4.z() {
	ret i32 5
}

define i32 @Data.T4.s() {
	ret i32 0
}

define i32 @Data.T4.a() {
	ret i32 0
}

define i32 @Data.T4.b() {
	ret i32 0
}

define ptr @__global__Data.test3() {
	%size0 = ptrtoint %Data.T3_vtable* getelementptr (%Data.T3_vtable, %Data.T3_vtable* null, i32 1) to i64
	%ptr_Data.T3_vtable_0 = call ptr @malloc(i64 %size0)
	%ptr_Data.T3_vtable_index3_0 = getelementptr %Data.T3_vtable, ptr %ptr_Data.T3_vtable_0, i32 0, i32 3
	store ptr @Data.T3.s, ptr %ptr_Data.T3_vtable_index3_0
	%ptr_Data.T3_vtable_index2_0 = getelementptr %Data.T3_vtable, ptr %ptr_Data.T3_vtable_0, i32 0, i32 2
	store ptr @Data.T3.z, ptr %ptr_Data.T3_vtable_index2_0
	%ptr_Data.T3_vtable_index0_0 = getelementptr %Data.T3_vtable, ptr %ptr_Data.T3_vtable_0, i32 0, i32 0
	store ptr @Data.T3.x, ptr %ptr_Data.T3_vtable_index0_0
	%ptr_Data.T3_vtable_index1_0 = getelementptr %Data.T3_vtable, ptr %ptr_Data.T3_vtable_0, i32 0, i32 1
	store ptr @Data.T3.y, ptr %ptr_Data.T3_vtable_index1_0
	ret ptr %ptr_Data.T3_vtable_0
}

define i32 @__global__Data.a() {
	%v3 = call ptr @__global__Data.test3()
	%ptr_Data.T3_vtable_index0_1 = getelementptr %Data.T3_vtable, ptr %v3, i32 0, i32 0
	%ptr_Data.T3_fun0 = load ptr, ptr %ptr_Data.T3_vtable_index0_1
	%v4 = call i32 %ptr_Data.T3_fun0()
	ret i32 %v4
}

define i32 @main() {
	%v5 = call i32 @__global__Data.a()
	ret i32 %v5
}