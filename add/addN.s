	.text
	.p2align	5
	.globl	_test_add
	.globl	test_add
_test_add:
test_add:
	movq	%rsp, %r10
	leaq	-8(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rdi, (%rsp)
	movq	(%rsi), %rax
	movq	(%rdx), %rcx
	movq	$0, %rdx
	addq	%rcx, %rax
	adcq	$0, %rdx
	movq	(%rsp), %rcx
	movq	%rax, (%rcx)
	movq	%rdx, 8(%rcx)
	movq	%r10, %rsp
	ret 
