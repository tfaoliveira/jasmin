	.text
	.p2align	5
	.globl	_test_add
	.globl	test_add
_test_add:
test_add:
	movq	%rsp, %rax
	leaq	-48(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, (%rsp)
	movq	%rbx, 8(%rsp)
	movq	%rbp, 16(%rsp)
	movq	%r12, 24(%rsp)
	movq	%r13, 32(%rsp)
	movq	%r14, 40(%rsp)
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %r9
	movq	32(%rsi), %r10
	movq	40(%rsi), %rsi
	movq	(%rdx), %r11
	movq	8(%rdx), %rbp
	movq	16(%rdx), %rbx
	movq	24(%rdx), %r12
	movq	32(%rdx), %r13
	movq	40(%rdx), %rdx
	movq	$0, %r14
	addq	%r11, %rax
	adcq	%rbp, %rcx
	adcq	%rbx, %r8
	adcq	%r12, %r9
	adcq	%r13, %r10
	adcq	%rdx, %rsi
	adcq	$0, %r14
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%r9, 24(%rdi)
	movq	%r10, 32(%rdi)
	movq	%rsi, 40(%rdi)
	movq	%r14, 48(%rdi)
	movq	8(%rsp), %rbx
	movq	16(%rsp), %rbp
	movq	24(%rsp), %r12
	movq	32(%rsp), %r13
	movq	40(%rsp), %r14
	movq	(%rsp), %rsp
	ret 
