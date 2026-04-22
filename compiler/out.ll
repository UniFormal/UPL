define i32 @main() {
	%u1 = icmp eq i32 5, 5
	%v1 = zext i1 %u1 to i32
	ret i32 %v1
}