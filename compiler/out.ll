define i32 @main() {
	%u1 = icmp eq i32 3, 5
	%u2 = zext i1 %u1 to i32
	%u3 = trunc i32 %u2 to i1
	br i1 %u3, label %then, label %else
then:
	br label %end
else:
	br label %end
end:
	%u4 = phi i32 [ 5, %then ], [ 3, %else ]
	ret i32 %u4
}