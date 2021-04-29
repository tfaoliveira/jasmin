	.text
	.p2align	5
	.globl	_test_add4
	.globl	test_add4
_test_add4:
test_add4:
	movq	%rsp, %rax
	leaq	-16(%rsp), %rsp
	andq	$-8, %rsp
	movq	%rax, (%rsp)
	movq	%rbp, 8(%rsp)
	movq	(%rsi), %rax
	movq	8(%rsi), %rcx
	movq	16(%rsi), %r8
	movq	24(%rsi), %rsi
	movq	(%rdx), %r9
	movq	8(%rdx), %r10
	movq	16(%rdx), %r11
	movq	24(%rdx), %rdx
	movq	$0, %rbp
	addq	%r9, %rax
	adcq	%r10, %rcx
	adcq	%r11, %r8
	adcq	%rdx, %rsi
	adcq	$0, %rbp
	movq	%rax, (%rdi)
	movq	%rcx, 8(%rdi)
	movq	%r8, 16(%rdi)
	movq	%rsi, 24(%rdi)
	movq	%rbp, 32(%rdi)
	movq	8(%rsp), %rbp
	movq	(%rsp), %rsp
	ret 
