SECTION .text
	GLOBAL fiat_bls24_509_p_mul
fiat_bls24_509_p_mul:
sub rsp, 2544
mov rax, rdx; preserving value of arg2 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mulx r11, r10, [ rax + 0x38 ]; hix395, lox394<- arg1[4] * arg2[7]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r8, rcx, [ rax + 0x0 ]; hix308, lox307<- arg1[3] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mulx rbx, r9, [ rsi + 0x30 ]; hix597, lox596<- arg1[6] * arg2[7]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mulx r12, rbp, [ rax + 0x30 ]; hix397, lox396<- arg1[4] * arg2[6]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mulx r14, r13, [ rsi + 0x0 ]; hix22, lox21<- arg1[0] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mulx rdi, r15, [ rax + 0x8 ]; hix104, lox103<- arg1[1] * arg2[1]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x48 ], r11; spilling x395 to mem
mov [ rsp - 0x40 ], r10; spilling x394 to mem
mulx r10, r11, [ rax + 0x8 ]; hix407, lox406<- arg1[4] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp - 0x38 ], r12; spilling x397 to mem
mov [ rsp - 0x30 ], rcx; spilling x307 to mem
mulx rcx, r12, [ rax + 0x0 ]; hix106, lox105<- arg1[1] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp - 0x28 ], rbp; spilling x396 to mem
mov [ rsp - 0x20 ], rbx; spilling x597 to mem
mulx rbx, rbp, [ rsi + 0x18 ]; hix294, lox293<- arg1[3] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp - 0x18 ], r9; spilling x596 to mem
mov [ rsp - 0x10 ], r12; spilling x105 to mem
mulx r12, r9, [ rax + 0x18 ]; hix605, lox604<- arg1[6] * arg2[3]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x8 ], rbx; spilling x294 to mem
mov [ rsp + 0x0 ], r14; spilling x22 to mem
mulx r14, rbx, [ rax + 0x30 ]; hix296, lox295<- arg1[3] * arg2[6]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x8 ], rbp; spilling x293 to mem
mov [ rsp + 0x10 ], r14; spilling x296 to mem
mulx r14, rbp, [ rsi + 0x18 ]; hix302, lox301<- arg1[3] * arg2[3]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x18 ], rbx; spilling x295 to mem
mov [ rsp + 0x20 ], r14; spilling x302 to mem
mulx r14, rbx, [ rsi + 0x30 ]; hix603, lox602<- arg1[6] * arg2[4]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x28 ], r14; spilling x603 to mem
mov [ rsp + 0x30 ], rbp; spilling x301 to mem
mulx rbp, r14, [ rax + 0x10 ]; hix405, lox404<- arg1[4] * arg2[2]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x38 ], rbp; spilling x405 to mem
mov [ rsp + 0x40 ], r8; spilling x308 to mem
mulx r8, rbp, [ rsi + 0x10 ]; hix207, lox206<- arg1[2] * arg2[0]
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x48 ], rbp; spilling x206 to mem
mov [ rsp + 0x50 ], rbx; spilling x602 to mem
mulx rbx, rbp, [ rsi + 0x20 ]; hix409, lox408<- arg1[4] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x58 ], rbp; spilling x408 to mem
mov [ rsp + 0x60 ], r12; spilling x605 to mem
mulx r12, rbp, [ rax + 0x30 ]; hix498, lox497<- arg1[5] * arg2[6]
mov rdx, [ rax + 0x18 ]; arg2[3] to rdx
mov [ rsp + 0x68 ], r12; spilling x498 to mem
mov [ rsp + 0x70 ], rbp; spilling x497 to mem
mulx rbp, r12, [ rsi + 0x0 ]; hix18, lox17<- arg1[0] * arg2[3]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x78 ], rbp; spilling x18 to mem
mov [ rsp + 0x80 ], r12; spilling x17 to mem
mulx r12, rbp, [ rax + 0x8 ]; hix508, lox507<- arg1[5] * arg2[1]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x88 ], r12; spilling x508 to mem
mov [ rsp + 0x90 ], rbp; spilling x507 to mem
mulx rbp, r12, [ rax + 0x0 ]; hix24, lox23<- arg1[0] * arg2[0]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x98 ], r9; spilling x604 to mem
mov [ rsp + 0xa0 ], r14; spilling x404 to mem
mulx r14, r9, [ rsi + 0x38 ]; hix700, lox699<- arg1[7] * arg2[6]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0xa8 ], r14; spilling x700 to mem
mov [ rsp + 0xb0 ], r9; spilling x699 to mem
mulx r9, r14, [ rsi + 0x8 ]; hix98, lox97<- arg1[1] * arg2[4]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xb8 ], r9; spilling x98 to mem
mov [ rsp + 0xc0 ], r14; spilling x97 to mem
mulx r14, r9, [ rax + 0x10 ]; hix506, lox505<- arg1[5] * arg2[2]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0xc8 ], r14; spilling x506 to mem
mov [ rsp + 0xd0 ], r9; spilling x505 to mem
mulx r9, r14, [ rsi + 0x0 ]; hix20, lox19<- arg1[0] * arg2[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xd8 ], r9; spilling x20 to mem
mov [ rsp + 0xe0 ], r14; spilling x19 to mem
mulx r14, r9, [ rax + 0x28 ]; hix14, lox13<- arg1[0] * arg2[5]
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0xe8 ], r14; spilling x14 to mem
mov [ rsp + 0xf0 ], r9; spilling x13 to mem
mulx r9, r14, [ rsi + 0x10 ]; hix205, lox204<- arg1[2] * arg2[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0xf8 ], r9; spilling x205 to mem
mov [ rsp + 0x100 ], r10; spilling x407 to mem
mulx r10, r9, [ rax + 0x10 ]; hix102, lox101<- arg1[1] * arg2[2]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x108 ], r10; spilling x102 to mem
mov [ rsp + 0x110 ], r11; spilling x406 to mem
mulx r11, r10, [ rsi + 0x10 ]; hix193, lox192<- arg1[2] * arg2[7]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x118 ], r11; spilling x193 to mem
mov [ rsp + 0x120 ], r10; spilling x192 to mem
mulx r10, r11, [ rax + 0x30 ]; hix599, lox598<- arg1[6] * arg2[6]
test al, al
adox r14, r8
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x128 ], r14; spilling x208 to mem
mulx r14, r8, [ rax + 0x28 ]; hix399, lox398<- arg1[4] * arg2[5]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x130 ], r14; spilling x399 to mem
mov [ rsp + 0x138 ], r8; spilling x398 to mem
mulx r8, r14, [ rax + 0x18 ]; hix100, lox99<- arg1[1] * arg2[3]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x140 ], r10; spilling x599 to mem
mov [ rsp + 0x148 ], r11; spilling x598 to mem
mulx r11, r10, [ rax + 0x38 ]; hix10, lox9<- arg1[0] * arg2[7]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x150 ], r11; spilling x10 to mem
mov [ rsp + 0x158 ], r10; spilling x9 to mem
mulx r10, r11, [ rax + 0x28 ]; hix500, lox499<- arg1[5] * arg2[5]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x160 ], r10; spilling x500 to mem
mov [ rsp + 0x168 ], r11; spilling x499 to mem
mulx r11, r10, [ rax + 0x30 ]; hix12, lox11<- arg1[0] * arg2[6]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x170 ], r11; spilling x12 to mem
mov [ rsp + 0x178 ], r10; spilling x11 to mem
mulx r10, r11, [ rax + 0x18 ]; hix706, lox705<- arg1[7] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x180 ], r10; spilling x706 to mem
mov [ rsp + 0x188 ], r8; spilling x100 to mem
mulx r8, r10, [ rsi + 0x30 ]; hix607, lox606<- arg1[6] * arg2[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x190 ], r14; spilling x99 to mem
mov [ rsp + 0x198 ], r11; spilling x705 to mem
mulx r11, r14, [ rax + 0x28 ]; hix702, lox701<- arg1[7] * arg2[5]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov [ rsp + 0x1a0 ], r11; spilling x702 to mem
mov [ rsp + 0x1a8 ], r14; spilling x701 to mem
mulx r14, r11, [ rsi + 0x18 ]; hix304, lox303<- arg1[3] * arg2[2]
mov rdx, 0x6efa1180a5fe67fd ; moving imm to reg
mov [ rsp + 0x1b0 ], r14; spilling x304 to mem
mov [ rsp + 0x1b8 ], r11; spilling x303 to mem
mulx r11, r14, r12; hi_, lox40<- x23 * 0x6efa1180a5fe67fd
mov rdx, [ rax + 0x8 ]; arg2[1] to rdx
mov [ rsp + 0x1c0 ], r8; spilling x607 to mem
mulx r8, r11, [ rsi + 0x30 ]; hix609, lox608<- arg1[6] * arg2[1]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x1c8 ], r10; spilling x606 to mem
mov [ rsp + 0x1d0 ], r8; spilling x609 to mem
mulx r8, r10, [ rax + 0x0 ]; hix611, lox610<- arg1[6] * arg2[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x1d8 ], r10; spilling x610 to mem
mov [ rsp + 0x1e0 ], r11; spilling x608 to mem
mulx r11, r10, [ rax + 0x18 ]; hix504, lox503<- arg1[5] * arg2[3]
mov rdx, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x1e8 ], r11; spilling x504 to mem
mov [ rsp + 0x1f0 ], r10; spilling x503 to mem
mulx r10, r11, r14; hix57, lox56<- x40 * 0xa13d118db8bfd2ab
adcx r13, rbp
seto bpl;
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, rcx
mov rcx, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov rdx, r14; x40 to rdx
mov [ rsp + 0x1f8 ], r15; spilling x107 to mem
mulx r15, r14, rcx; hix45, lox44<- x40 * 0xfcedf2b4f9c0ecf6
adox r9, rdi
seto dil;
mov rcx, -0x2 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r11, r12
mov r11, rdx; preserving value of x40 into a new reg
mov rdx, [ rax + 0x8 ]; saving arg2[1] in rdx.
mulx rcx, r12, [ rsi + 0x38 ]; hix710, lox709<- arg1[7] * arg2[1]
mov rdx, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x200 ], r9; spilling x109 to mem
mov [ rsp + 0x208 ], r15; spilling x45 to mem
mulx r15, r9, r11; hix51, lox50<- x40 * 0x626e85bf7c18a0f0
mov rdx, [ rax + 0x0 ]; arg2[0] to rdx
mov [ rsp + 0x210 ], r14; spilling x44 to mem
mov [ rsp + 0x218 ], r15; spilling x51 to mem
mulx r15, r14, [ rsi + 0x38 ]; hix712, lox711<- arg1[7] * arg2[0]
setc dl;
clc;
adcx rbx, [ rsp + 0x110 ]
mov [ rsp + 0x220 ], r14; spilling x711 to mem
mov r14, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, r14; 0x32ea0103e01090bb, swapping with x26, which is currently in rdx
mov [ rsp + 0x228 ], rbx; spilling x410 to mem
mov [ rsp + 0x230 ], r9; spilling x50 to mem
mulx r9, rbx, r11; hix49, lox48<- x40 * 0x32ea0103e01090bb
setc dl;
clc;
adcx r12, r15
mov r15, [ rsp + 0xa0 ]; load m64 x404 to register64
mov [ rsp + 0x238 ], r12; spilling x713 to mem
setc r12b;
clc;
mov [ rsp + 0x240 ], r9; spilling x49 to mem
mov r9, -0x1 ; moving imm to reg
movzx rdx, dl
adcx rdx, r9; loading flag
adcx r15, [ rsp + 0x100 ]
mov rdx, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x248 ], r15; spilling x412 to mem
mulx r15, r9, r11; hix55, lox54<- x40 * 0xee63bd076e8d9300
setc dl;
clc;
adcx r8, [ rsp + 0x1e0 ]
mov [ rsp + 0x250 ], r8; spilling x612 to mem
setc r8b;
clc;
adcx r9, r10
mov r10b, dl; preserving value of x413 into a new reg
mov rdx, [ rax + 0x28 ]; saving arg2[5] in rdx.
mov [ rsp + 0x258 ], rbx; spilling x48 to mem
mov [ rsp + 0x260 ], r9; spilling x58 to mem
mulx r9, rbx, [ rsi + 0x18 ]; hix298, lox297<- arg1[3] * arg2[5]
mov rdx, [ rsp + 0x1d0 ]; load m64 x609 to register64
mov byte [ rsp + 0x268 ], r10b; spilling byte x413 to mem
setc r10b;
clc;
mov [ rsp + 0x270 ], r13; spilling x25 to mem
mov r13, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, r13; loading flag
adcx rdx, [ rsp + 0x1c8 ]
mov r8, [ rsp + 0x98 ]; load m64 x604 to register64
adcx r8, [ rsp + 0x1c0 ]
mov r13, rdx; preserving value of x614 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x278 ], r8; spilling x616 to mem
mov byte [ rsp + 0x280 ], r14b; spilling byte x26 to mem
mulx r14, r8, [ rax + 0x8 ]; hix306, lox305<- arg1[3] * arg2[1]
mov rdx, [ rsp + 0x50 ]; load m64 x602 to register64
adcx rdx, [ rsp + 0x60 ]
mov [ rsp + 0x288 ], rdx; spilling x618 to mem
setc dl;
clc;
adcx r8, [ rsp + 0x40 ]
mov [ rsp + 0x290 ], r13; spilling x614 to mem
mov r13b, dl; preserving value of x619 into a new reg
mov rdx, [ rax + 0x18 ]; saving arg2[3] in rdx.
mov [ rsp + 0x298 ], r8; spilling x309 to mem
mov [ rsp + 0x2a0 ], r15; spilling x55 to mem
mulx r15, r8, [ rsi + 0x10 ]; hix201, lox200<- arg1[2] * arg2[3]
mov rdx, [ rax + 0x10 ]; arg2[2] to rdx
mov byte [ rsp + 0x2a8 ], r10b; spilling byte x59 to mem
mov byte [ rsp + 0x2b0 ], r13b; spilling byte x619 to mem
mulx r13, r10, [ rsi + 0x10 ]; hix203, lox202<- arg1[2] * arg2[2]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov [ rsp + 0x2b8 ], r15; spilling x201 to mem
mov byte [ rsp + 0x2c0 ], dil; spilling byte x110 to mem
mulx rdi, r15, [ rsi + 0x18 ]; hix300, lox299<- arg1[3] * arg2[4]
seto dl;
mov [ rsp + 0x2c8 ], rcx; spilling x710 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, rcx; loading flag
adox r10, [ rsp + 0xf8 ]
adcx r14, [ rsp + 0x1b8 ]
mov rbp, [ rsp + 0x1b0 ]; load m64 x304 to register64
adcx rbp, [ rsp + 0x30 ]
adcx r15, [ rsp + 0x20 ]
adox r8, r13
adcx rbx, rdi
adcx r9, [ rsp + 0x18 ]
mov r13b, dl; preserving value of x74 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx rcx, rdi, [ rax + 0x10 ]; hix708, lox707<- arg1[7] * arg2[2]
mov rdx, [ rax + 0x28 ]; arg2[5] to rdx
mov [ rsp + 0x2d0 ], r9; spilling x319 to mem
mov [ rsp + 0x2d8 ], rbx; spilling x317 to mem
mulx rbx, r9, [ rsi + 0x8 ]; hix96, lox95<- arg1[1] * arg2[5]
seto dl;
mov [ rsp + 0x2e0 ], r15; spilling x315 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r15; loading flag
adox rdi, [ rsp + 0x2c8 ]
mov r12, [ rsp + 0x10 ]; load m64 x296 to register64
adcx r12, [ rsp + 0x8 ]
adox rcx, [ rsp + 0x198 ]
mov r15, [ rsp + 0x108 ]; load m64 x102 to register64
mov [ rsp + 0x2e8 ], rcx; spilling x717 to mem
seto cl;
mov [ rsp + 0x2f0 ], rdi; spilling x715 to mem
movzx rdi, byte [ rsp + 0x2c0 ]; load byte memx110 to register64
mov [ rsp + 0x2f8 ], r12; spilling x321 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rdi, r12; loading flag
adox r15, [ rsp + 0x190 ]
mov rdi, [ rsp + 0x188 ]; load m64 x100 to register64
adox rdi, [ rsp + 0xc0 ]
mov r12b, dl; preserving value of x213 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x300 ], rbp; spilling x313 to mem
mov [ rsp + 0x308 ], r14; spilling x311 to mem
mulx r14, rbp, [ rax + 0x20 ]; hix199, lox198<- arg1[2] * arg2[4]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x310 ], r8; spilling x212 to mem
mov [ rsp + 0x318 ], r10; spilling x210 to mem
mulx r10, r8, [ rax + 0x28 ]; hix601, lox600<- arg1[6] * arg2[5]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x320 ], rdi; spilling x113 to mem
mov [ rsp + 0x328 ], r15; spilling x111 to mem
mulx r15, rdi, [ rax + 0x20 ]; hix704, lox703<- arg1[7] * arg2[4]
seto dl;
mov [ rsp + 0x330 ], r10; spilling x601 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r10; loading flag
adox rbp, [ rsp + 0x2b8 ]
setc r12b;
movzx r10, byte [ rsp + 0x2b0 ]; load byte memx619 to register64
clc;
mov [ rsp + 0x338 ], rbp; spilling x214 to mem
mov rbp, -0x1 ; moving imm to reg
adcx r10, rbp; loading flag
adcx r8, [ rsp + 0x28 ]
seto r10b;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, rbp; loading flag
adox r9, [ rsp + 0xb8 ]
seto dl;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbp; loading flag
adox rdi, [ rsp + 0x180 ]
adox r15, [ rsp + 0x1a8 ]
mov cl, dl; preserving value of x116 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x340 ], r15; spilling x721 to mem
mulx r15, rbp, [ rsi + 0x0 ]; hix16, lox15<- arg1[0] * arg2[4]
mov rdx, [ rsp + 0x1a0 ]; load m64 x702 to register64
adox rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x348 ], rdi; spilling x719 to mem
mov rdi, rdx; preserving value of x723 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x350 ], r8; spilling x620 to mem
mov [ rsp + 0x358 ], r9; spilling x115 to mem
mulx r9, r8, [ rax + 0x28 ]; hix197, lox196<- arg1[2] * arg2[5]
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x360 ], rdi; spilling x723 to mem
mov [ rsp + 0x368 ], r15; spilling x16 to mem
mulx r15, rdi, [ rsi + 0x10 ]; hix195, lox194<- arg1[2] * arg2[6]
seto dl;
mov [ rsp + 0x370 ], r15; spilling x195 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r15; loading flag
adox r14, r8
mov r10, 0xcfcb5c6071bad3d2 ; moving imm to reg
xchg rdx, r11; x40, swapping with x724, which is currently in rdx
mulx r15, r8, r10; hix53, lox52<- x40 * 0xcfcb5c6071bad3d2
adox rdi, r9
setc r9b;
movzx r10, byte [ rsp + 0x2a8 ]; load byte memx59 to register64
clc;
mov [ rsp + 0x378 ], rdi; spilling x218 to mem
mov rdi, -0x1 ; moving imm to reg
adcx r10, rdi; loading flag
adcx r8, [ rsp + 0x2a0 ]
mov r10, [ rsp + 0xe0 ]; load m64 x19 to register64
seto dil;
mov [ rsp + 0x380 ], r14; spilling x216 to mem
movzx r14, byte [ rsp + 0x280 ]; load byte memx26 to register64
mov byte [ rsp + 0x388 ], r9b; spilling byte x621 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r9; loading flag
adox r10, [ rsp + 0x0 ]
movzx r14, r12b;
mov r9, [ rsp - 0x8 ]; load m64 x294 to register64
lea r14, [ r14 + r9 ]; r8/64 + m8
mov r9, [ rsp + 0x270 ]; load m64 x25 to register64
seto r12b;
mov [ rsp + 0x390 ], r14; spilling x323 to mem
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox r9, [ rsp + 0x260 ]
seto r13b;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp - 0x10 ]
mov r14, [ rsp + 0x80 ]; load m64 x17 to register64
mov byte [ rsp + 0x398 ], r11b; spilling byte x724 to mem
setc r11b;
clc;
mov byte [ rsp + 0x3a0 ], dil; spilling byte x219 to mem
mov rdi, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, rdi; loading flag
adcx r14, [ rsp + 0xd8 ]
mov r12, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r12; 0x6efa1180a5fe67fd, swapping with x40, which is currently in rdx
mov [ rsp + 0x3a8 ], r14; spilling x29 to mem
mulx r14, rdi, r9; hi_, lox140<- x122 * 0x6efa1180a5fe67fd
mov r14, 0xa13d118db8bfd2ab ; moving imm to reg
mov rdx, rdi; x140 to rdx
mov [ rsp + 0x3b0 ], r8; spilling x60 to mem
mulx r8, rdi, r14; hix157, lox156<- x140 * 0xa13d118db8bfd2ab
adcx rbp, [ rsp + 0x78 ]
seto r14b;
mov [ rsp + 0x3b8 ], rbp; spilling x31 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rbp; loading flag
adox r15, [ rsp + 0x230 ]
mov r11, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x3c0 ], r8; spilling x157 to mem
mulx r8, rbp, r11; hix155, lox154<- x140 * 0xee63bd076e8d9300
mov r11, [ rsp + 0x218 ]; load m64 x51 to register64
adox r11, [ rsp + 0x258 ]
mov [ rsp + 0x3c8 ], r11; spilling x64 to mem
mov r11, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x3d0 ], r8; spilling x155 to mem
mov [ rsp + 0x3d8 ], rbp; spilling x154 to mem
mulx rbp, r8, r11; hix153, lox152<- x140 * 0xcfcb5c6071bad3d2
mov r11, rdx; preserving value of x140 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x3e0 ], rbp; spilling x153 to mem
mov [ rsp + 0x3e8 ], r8; spilling x152 to mem
mulx r8, rbp, [ rax + 0x0 ]; hix510, lox509<- arg1[5] * arg2[0]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x3f0 ], rbp; spilling x509 to mem
mov [ rsp + 0x3f8 ], rdi; spilling x156 to mem
mulx rdi, rbp, [ rsi + 0x38 ]; hix698, lox697<- arg1[7] * arg2[7]
mov rdx, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x400 ], r8; spilling x510 to mem
mov [ rsp + 0x408 ], rdi; spilling x698 to mem
mulx rdi, r8, r11; hix149, lox148<- x140 * 0x32ea0103e01090bb
mov rdx, [ rax + 0x30 ]; arg2[6] to rdx
mov [ rsp + 0x410 ], rdi; spilling x149 to mem
mov [ rsp + 0x418 ], r8; spilling x148 to mem
mulx r8, rdi, [ rsi + 0x8 ]; hix94, lox93<- arg1[1] * arg2[6]
seto dl;
mov [ rsp + 0x420 ], r8; spilling x94 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r8; loading flag
adox rbx, rdi
mov rcx, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
xchg rdx, r11; x140, swapping with x65, which is currently in rdx
mulx r8, rdi, rcx; hix145, lox144<- x140 * 0xfcedf2b4f9c0ecf6
setc cl;
clc;
mov [ rsp + 0x428 ], rbx; spilling x117 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rbx; loading flag
adcx r10, [ rsp + 0x3b0 ]
seto r13b;
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rbx; loading flag
adox r10, [ rsp + 0x1f8 ]
mov r14, [ rsp + 0x370 ]; load m64 x195 to register64
setc bl;
mov [ rsp + 0x430 ], r8; spilling x145 to mem
movzx r8, byte [ rsp + 0x3a0 ]; load byte memx219 to register64
clc;
mov [ rsp + 0x438 ], r10; spilling x124 to mem
mov r10, -0x1 ; moving imm to reg
adcx r8, r10; loading flag
adcx r14, [ rsp + 0x120 ]
seto r8b;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r10; loading flag
adox r15, [ rsp + 0x3a8 ]
setc bl;
movzx r10, byte [ rsp + 0x398 ]; load byte memx724 to register64
clc;
mov [ rsp + 0x440 ], r14; spilling x220 to mem
mov r14, -0x1 ; moving imm to reg
adcx r10, r14; loading flag
adcx rbp, [ rsp + 0xa8 ]
mov r10, [ rsp + 0x368 ]; load m64 x16 to register64
seto r14b;
mov [ rsp + 0x448 ], rbp; spilling x725 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbp; loading flag
adox r10, [ rsp + 0xf0 ]
mov rcx, [ rsp + 0x408 ];
mov rbp, 0x0 ; moving imm to reg
adcx rcx, rbp
mov rbp, [ rsp + 0xe8 ]; load m64 x14 to register64
adox rbp, [ rsp + 0x178 ]
mov [ rsp + 0x450 ], rcx; spilling x727 to mem
mov rcx, [ rsp + 0x170 ]; load m64 x12 to register64
adox rcx, [ rsp + 0x158 ]
mov byte [ rsp + 0x458 ], bl; spilling byte x221 to mem
mov rbx, [ rsp + 0x400 ]; load m64 x510 to register64
clc;
adcx rbx, [ rsp + 0x90 ]
mov [ rsp + 0x460 ], rbx; spilling x511 to mem
mov rbx, [ rsp + 0x88 ]; load m64 x508 to register64
adcx rbx, [ rsp + 0xd0 ]
mov [ rsp + 0x468 ], rbx; spilling x513 to mem
mov rbx, rdx; preserving value of x140 into a new reg
mov rdx, [ rax + 0x20 ]; saving arg2[4] in rdx.
mov [ rsp + 0x470 ], rcx; spilling x37 to mem
mov [ rsp + 0x478 ], rbp; spilling x35 to mem
mulx rbp, rcx, [ rsi + 0x28 ]; hix502, lox501<- arg1[5] * arg2[4]
mov rdx, [ rax + 0x38 ]; arg2[7] to rdx
mov [ rsp + 0x480 ], r10; spilling x33 to mem
mov [ rsp + 0x488 ], rdi; spilling x144 to mem
mulx rdi, r10, [ rsi + 0x28 ]; hix496, lox495<- arg1[5] * arg2[7]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x490 ], rdi; spilling x496 to mem
mov byte [ rsp + 0x498 ], r14b; spilling byte x80 to mem
mulx r14, rdi, [ rax + 0x38 ]; hix92, lox91<- arg1[1] * arg2[7]
mov rdx, [ rsp + 0xc8 ]; load m64 x506 to register64
adcx rdx, [ rsp + 0x1f0 ]
mov [ rsp + 0x4a0 ], r14; spilling x92 to mem
mov r14, rdx; preserving value of x515 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x4a8 ], r15; spilling x79 to mem
mov byte [ rsp + 0x4b0 ], r8b; spilling byte x125 to mem
mulx r8, r15, [ rax + 0x18 ]; hix403, lox402<- arg1[4] * arg2[3]
adcx rcx, [ rsp + 0x1e8 ]
mov rdx, [ rsp + 0x330 ]; load m64 x601 to register64
mov [ rsp + 0x4b8 ], rcx; spilling x517 to mem
seto cl;
mov [ rsp + 0x4c0 ], r14; spilling x515 to mem
movzx r14, byte [ rsp + 0x388 ]; load byte memx621 to register64
mov [ rsp + 0x4c8 ], r8; spilling x403 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r8; loading flag
adox rdx, [ rsp + 0x148 ]
seto r14b;
movzx r8, byte [ rsp + 0x268 ]; load byte memx413 to register64
mov [ rsp + 0x4d0 ], rdx; spilling x622 to mem
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
adox r8, rdx; loading flag
adox r15, [ rsp + 0x38 ]
seto r8b;
inc rdx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdx, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rdx; loading flag
adox rdi, [ rsp + 0x420 ]
mov r13, 0xcb8ac8495d187e8c ; moving imm to reg
mov rdx, r13; 0xcb8ac8495d187e8c to rdx
mov [ rsp + 0x4d8 ], r15; spilling x414 to mem
mulx r15, r13, r12; hix47, lox46<- x40 * 0xcb8ac8495d187e8c
adcx rbp, [ rsp + 0x168 ]
setc dl;
clc;
adcx r9, [ rsp + 0x3f8 ]
mov r9, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r9; 0x155556ffff39ca9b, swapping with x520, which is currently in rdx
mov [ rsp + 0x4e0 ], rbp; spilling x519 to mem
mov [ rsp + 0x4e8 ], rdi; spilling x119 to mem
mulx rdi, rbp, r12; hix43, lox42<- x40 * 0x155556ffff39ca9b
seto r12b;
mov rdx, -0x1 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rdx; loading flag
adox r13, [ rsp + 0x240 ]
mov rdx, [ rax + 0x20 ]; arg2[4] to rdx
mov byte [ rsp + 0x4f0 ], r12b; spilling byte x120 to mem
mulx r12, r11, [ rsi + 0x20 ]; hix401, lox400<- arg1[4] * arg2[4]
adox r15, [ rsp + 0x210 ]
adox rbp, [ rsp + 0x208 ]
mov rdx, [ rsp + 0x3d8 ]; load m64 x154 to register64
mov [ rsp + 0x4f8 ], r12; spilling x401 to mem
seto r12b;
mov [ rsp + 0x500 ], r11; spilling x400 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdx, [ rsp + 0x3c0 ]
mov r11, [ rsp + 0x140 ]; load m64 x599 to register64
mov byte [ rsp + 0x508 ], r8b; spilling byte x415 to mem
seto r8b;
mov byte [ rsp + 0x510 ], cl; spilling byte x38 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rcx; loading flag
adox r11, [ rsp - 0x18 ]
mov r14, [ rsp + 0x3d0 ]; load m64 x155 to register64
seto cl;
mov [ rsp + 0x518 ], r11; spilling x624 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, r11; loading flag
adox r14, [ rsp + 0x3e8 ]
mov r8, [ rsp + 0x160 ]; load m64 x500 to register64
setc r11b;
clc;
mov byte [ rsp + 0x520 ], cl; spilling byte x625 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rcx; loading flag
adcx r8, [ rsp + 0x70 ]
adcx r10, [ rsp + 0x68 ]
movzx r9, r12b;
lea r9, [ r9 + rdi ]
mov rdi, [ rsp + 0x200 ]; load m64 x109 to register64
setc r12b;
movzx rcx, byte [ rsp + 0x4b0 ]; load byte memx125 to register64
clc;
mov [ rsp + 0x528 ], r10; spilling x523 to mem
mov r10, -0x1 ; moving imm to reg
adcx rcx, r10; loading flag
adcx rdi, [ rsp + 0x4a8 ]
mov rcx, 0x626e85bf7c18a0f0 ; moving imm to reg
xchg rdx, rcx; 0x626e85bf7c18a0f0, swapping with x158, which is currently in rdx
mov byte [ rsp + 0x530 ], r12b; spilling byte x524 to mem
mulx r12, r10, rbx; hix151, lox150<- x140 * 0x626e85bf7c18a0f0
mov rdx, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x538 ], r8; spilling x521 to mem
mov [ rsp + 0x540 ], r9; spilling x72 to mem
mulx r9, r8, rbx; hix147, lox146<- x140 * 0xcb8ac8495d187e8c
mov rdx, [ rsp + 0x3b8 ]; load m64 x31 to register64
mov [ rsp + 0x548 ], r14; spilling x160 to mem
setc r14b;
mov [ rsp + 0x550 ], rdi; spilling x126 to mem
movzx rdi, byte [ rsp + 0x498 ]; load byte memx80 to register64
clc;
mov [ rsp + 0x558 ], rbp; spilling x70 to mem
mov rbp, -0x1 ; moving imm to reg
adcx rdi, rbp; loading flag
adcx rdx, [ rsp + 0x3c8 ]
adox r10, [ rsp + 0x3e0 ]
adox r12, [ rsp + 0x418 ]
adox r8, [ rsp + 0x410 ]
adox r9, [ rsp + 0x488 ]
adcx r13, [ rsp + 0x480 ]
adcx r15, [ rsp + 0x478 ]
setc dil;
clc;
movzx r14, r14b
adcx r14, rbp; loading flag
adcx rdx, [ rsp + 0x328 ]
seto r14b;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rbp; loading flag
adox rcx, [ rsp + 0x438 ]
adcx r13, [ rsp + 0x320 ]
mov r11, [ rsp + 0x558 ]; load m64 x70 to register64
setc bpl;
clc;
mov [ rsp + 0x560 ], r9; spilling x168 to mem
mov r9, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r9; loading flag
adcx r11, [ rsp + 0x470 ]
mov rdi, [ rsp + 0x548 ]; load m64 x160 to register64
adox rdi, [ rsp + 0x550 ]
mov r9, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r9; 0x155556ffff39ca9b, swapping with x128, which is currently in rdx
mov [ rsp + 0x568 ], r8; spilling x166 to mem
mov [ rsp + 0x570 ], r12; spilling x164 to mem
mulx r12, r8, rbx; hix143, lox142<- x140 * 0x155556ffff39ca9b
setc bl;
clc;
adcx rcx, [ rsp + 0x48 ]
mov rdx, 0x6efa1180a5fe67fd ; moving imm to reg
mov [ rsp + 0x578 ], r12; spilling x143 to mem
mov [ rsp + 0x580 ], r13; spilling x130 to mem
mulx r13, r12, rcx; hi_, lox241<- x223 * 0x6efa1180a5fe67fd
adox r10, r9
adcx rdi, [ rsp + 0x128 ]
setc r13b;
clc;
mov r9, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r9; loading flag
adcx r8, [ rsp + 0x430 ]
seto r14b;
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r9; loading flag
adox r15, [ rsp + 0x358 ]
mov rbp, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov rdx, r12; x241 to rdx
mulx r9, r12, rbp; hix254, lox253<- x241 * 0xcfcb5c6071bad3d2
adox r11, [ rsp + 0x428 ]
movzx rbp, byte [ rsp + 0x510 ];
mov [ rsp + 0x588 ], r9; spilling x254 to mem
mov r9, [ rsp + 0x150 ]; load m64 x10 to register64
lea rbp, [ rbp + r9 ]; r8/64 + m8
mov r9, [ rsp + 0x500 ]; load m64 x400 to register64
mov [ rsp + 0x590 ], r12; spilling x253 to mem
seto r12b;
mov [ rsp + 0x598 ], rdi; spilling x225 to mem
movzx rdi, byte [ rsp + 0x508 ]; load byte memx415 to register64
mov [ rsp + 0x5a0 ], r8; spilling x170 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdi, r8; loading flag
adox r9, [ rsp + 0x4c8 ]
seto dil;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r8; loading flag
adox rbp, [ rsp + 0x540 ]
mov rbx, [ rsp + 0x4f8 ]; load m64 x401 to register64
setc r8b;
clc;
mov [ rsp + 0x5a8 ], r9; spilling x416 to mem
mov r9, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r9; loading flag
adcx rbx, [ rsp + 0x138 ]
mov rdi, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x5b0 ], rbx; spilling x418 to mem
mulx rbx, r9, rdi; hix246, lox245<- x241 * 0xfcedf2b4f9c0ecf6
movzx rdi, byte [ rsp + 0x520 ];
mov [ rsp + 0x5b8 ], rbx; spilling x246 to mem
mov rbx, [ rsp - 0x20 ]; load m64 x597 to register64
lea rdi, [ rdi + rbx ]; r8/64 + m8
mov rbx, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x5c0 ], rdi; spilling x626 to mem
mov [ rsp + 0x5c8 ], r9; spilling x245 to mem
mulx r9, rdi, rbx; hix258, lox257<- x241 * 0xa13d118db8bfd2ab
setc bl;
clc;
adcx rdi, rcx
seto dil;
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rcx; loading flag
adox rbp, [ rsp + 0x4e8 ]
mov r12, [ rsp + 0x580 ]; load m64 x130 to register64
setc cl;
clc;
mov byte [ rsp + 0x5d0 ], r8b; spilling byte x171 to mem
mov r8, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r8; loading flag
adcx r12, [ rsp + 0x570 ]
setc r14b;
clc;
movzx r13, r13b
adcx r13, r8; loading flag
adcx r10, [ rsp + 0x318 ]
adcx r12, [ rsp + 0x310 ]
setc r13b;
clc;
movzx r14, r14b
adcx r14, r8; loading flag
adcx r15, [ rsp + 0x568 ]
mov r14, [ rsp + 0x130 ]; load m64 x399 to register64
seto r8b;
mov [ rsp + 0x5d8 ], r12; spilling x229 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r12; loading flag
adox r14, [ rsp - 0x28 ]
seto bl;
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r12; loading flag
adox r15, [ rsp + 0x338 ]
adcx r11, [ rsp + 0x560 ]
adcx rbp, [ rsp + 0x5a0 ]
mov r13, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x5e0 ], r14; spilling x420 to mem
mulx r14, r12, r13; hix256, lox255<- x241 * 0xee63bd076e8d9300
seto r13b;
mov [ rsp + 0x5e8 ], rbp; spilling x187 to mem
mov rbp, -0x2 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r12, r9
setc r9b;
clc;
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r11, [ rsp + 0x380 ]
movzx r13, byte [ rsp + 0x4f0 ];
mov rbp, [ rsp + 0x4a0 ]; load m64 x92 to register64
lea r13, [ r13 + rbp ]; r8/64 + m8
seto bpl;
mov [ rsp + 0x5f0 ], r11; spilling x233 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r11; loading flag
adox r12, [ rsp + 0x598 ]
seto cl;
inc r11; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp - 0x30 ]
seto r11b;
mov [ rsp + 0x5f8 ], r15; spilling x231 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
movzx r8, r8b
adox r8, r15; loading flag
adox r13, rdi
movzx rdi, byte [ rsp + 0x5d0 ];
mov r8, [ rsp + 0x578 ]; load m64 x143 to register64
lea rdi, [ rdi + r8 ]; r8/64 + m8
mov r8, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r12; x324, swapping with x241, which is currently in rdx
mov byte [ rsp + 0x600 ], r11b; spilling byte x325 to mem
mulx r11, r15, r8; hi_, lox342<- x324 * 0x6efa1180a5fe67fd
mov r11, 0xa13d118db8bfd2ab ; moving imm to reg
xchg rdx, r15; x342, swapping with x324, which is currently in rdx
mov [ rsp + 0x608 ], r10; spilling x227 to mem
mulx r10, r8, r11; hix359, lox358<- x342 * 0xa13d118db8bfd2ab
mov r11, [ rsp - 0x40 ]; load m64 x394 to register64
mov [ rsp + 0x610 ], r10; spilling x359 to mem
seto r10b;
mov byte [ rsp + 0x618 ], cl; spilling byte x277 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rcx; loading flag
adox r11, [ rsp - 0x38 ]
setc bl;
clc;
adcx r8, r15
mov r8, 0x32ea0103e01090bb ; moving imm to reg
mulx rcx, r15, r8; hix351, lox350<- x342 * 0x32ea0103e01090bb
mov r8, 0x626e85bf7c18a0f0 ; moving imm to reg
xchg rdx, r8; 0x626e85bf7c18a0f0, swapping with x342, which is currently in rdx
mov [ rsp + 0x620 ], r11; spilling x422 to mem
mov [ rsp + 0x628 ], rcx; spilling x351 to mem
mulx rcx, r11, r12; hix252, lox251<- x241 * 0x626e85bf7c18a0f0
mov rdx, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x630 ], r15; spilling x350 to mem
mov byte [ rsp + 0x638 ], bl; spilling byte x234 to mem
mulx rbx, r15, r8; hix357, lox356<- x342 * 0xee63bd076e8d9300
setc dl;
clc;
mov [ rsp + 0x640 ], rbx; spilling x357 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, rbx; loading flag
adcx r13, rdi
movzx r9, byte [ rsp + 0x458 ];
mov rdi, [ rsp + 0x118 ]; load m64 x193 to register64
lea r9, [ r9 + rdi ]; r8/64 + m8
movzx rdi, r10b;
mov rbx, 0x0 ; moving imm to reg
adcx rdi, rbx
mov r10, [ rsp - 0x48 ];
adox r10, rbx
mov rbx, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r8; x342, swapping with x376, which is currently in rdx
mov [ rsp + 0x648 ], r10; spilling x424 to mem
mov byte [ rsp + 0x650 ], r8b; spilling byte x376 to mem
mulx r8, r10, rbx; hix345, lox344<- x342 * 0x155556ffff39ca9b
add bpl, 0x7F; load flag from rm/8 into OF, clears other flag. NOTE, if operand1 is not a byte reg, this fails.
adox r14, [ rsp + 0x590 ]
movzx rbp, byte [ rsp + 0x618 ]; load byte memx277 to register64
mov rbx, -0x1 ; moving imm to reg
adcx rbp, rbx; loading flag
adcx r14, [ rsp + 0x608 ]
adox r11, [ rsp + 0x588 ]
mov rbp, 0xcb8ac8495d187e8c ; moving imm to reg
xchg rdx, rbp; 0xcb8ac8495d187e8c, swapping with x342, which is currently in rdx
mov [ rsp + 0x658 ], r8; spilling x345 to mem
mulx r8, rbx, r12; hix248, lox247<- x241 * 0xcb8ac8495d187e8c
mov rdx, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x660 ], r10; spilling x344 to mem
mov [ rsp + 0x668 ], r14; spilling x278 to mem
mulx r14, r10, r12; hix250, lox249<- x241 * 0x32ea0103e01090bb
adcx r11, [ rsp + 0x5d8 ]
adox r10, rcx
adcx r10, [ rsp + 0x5f8 ]
mov rcx, [ rsp + 0x5e8 ]; load m64 x187 to register64
setc dl;
mov [ rsp + 0x670 ], r10; spilling x282 to mem
movzx r10, byte [ rsp + 0x638 ]; load byte memx234 to register64
clc;
mov [ rsp + 0x678 ], r11; spilling x280 to mem
mov r11, -0x1 ; moving imm to reg
adcx r10, r11; loading flag
adcx rcx, [ rsp + 0x378 ]
adox rbx, r14
adox r8, [ rsp + 0x5c8 ]
mov r10, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r12; x241, swapping with x283, which is currently in rdx
mulx r11, r14, r10; hix244, lox243<- x241 * 0x155556ffff39ca9b
adox r14, [ rsp + 0x5b8 ]
adcx r13, [ rsp + 0x440 ]
mov rdx, 0x0 ; moving imm to reg
adox r11, rdx
adcx r9, rdi
dec rdx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r12, r12b
adox r12, rdx; loading flag
adox rbx, [ rsp + 0x5f0 ]
mov rdi, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov rdx, rdi; 0xcfcb5c6071bad3d2 to rdx
mulx r12, rdi, rbp; hix355, lox354<- x342 * 0xcfcb5c6071bad3d2
seto r10b;
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x610 ]
mov rdx, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x680 ], r11; spilling x273 to mem
mov [ rsp + 0x688 ], r9; spilling x239 to mem
mulx r9, r11, rbp; hix353, lox352<- x342 * 0x626e85bf7c18a0f0
seto dl;
mov [ rsp + 0x690 ], rbx; spilling x284 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rbx; loading flag
adox rcx, r8
adox r14, r13
seto r8b;
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r13, -0x1 ; moving imm to reg
movzx rdx, dl
adox rdx, r13; loading flag
adox rdi, [ rsp + 0x640 ]
adox r11, r12
adox r9, [ rsp + 0x630 ]
mov r10, [ rsp + 0x668 ]; load m64 x278 to register64
setc r12b;
movzx rdx, byte [ rsp + 0x600 ]; load byte memx325 to register64
clc;
adcx rdx, r13; loading flag
adcx r10, [ rsp + 0x298 ]
mov rdx, 0xcb8ac8495d187e8c ; moving imm to reg
mulx r13, rbx, rbp; hix349, lox348<- x342 * 0xcb8ac8495d187e8c
mov rdx, [ rsp + 0x678 ]; load m64 x280 to register64
adcx rdx, [ rsp + 0x308 ]
mov [ rsp + 0x698 ], r9; spilling x366 to mem
seto r9b;
mov [ rsp + 0x6a0 ], r11; spilling x364 to mem
movzx r11, byte [ rsp + 0x650 ]; load byte memx376 to register64
mov byte [ rsp + 0x6a8 ], r12b; spilling byte x240 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r11, r12; loading flag
adox r10, r15
mov r11, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
xchg rdx, rbp; x342, swapping with x328, which is currently in rdx
mulx r12, r15, r11; hix347, lox346<- x342 * 0xfcedf2b4f9c0ecf6
setc dl;
clc;
adcx r10, [ rsp + 0x58 ]
mov r11, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r11; 0x6efa1180a5fe67fd, swapping with x329, which is currently in rdx
mov [ rsp + 0x6b0 ], r12; spilling x347 to mem
mov [ rsp + 0x6b8 ], r15; spilling x346 to mem
mulx r15, r12, r10; hi_, lox443<- x425 * 0x6efa1180a5fe67fd
mov r15, 0xa13d118db8bfd2ab ; moving imm to reg
mov rdx, r12; x443 to rdx
mov [ rsp + 0x6c0 ], r13; spilling x349 to mem
mulx r13, r12, r15; hix460, lox459<- x443 * 0xa13d118db8bfd2ab
setc r15b;
clc;
adcx r12, r10
adox rdi, rbp
mov r12, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mulx r10, rbp, r12; hix448, lox447<- x443 * 0xfcedf2b4f9c0ecf6
setc r12b;
clc;
mov [ rsp + 0x6c8 ], r10; spilling x448 to mem
mov r10, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r10; loading flag
adcx rdi, [ rsp + 0x228 ]
mov r15, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x6d0 ], rbp; spilling x447 to mem
mulx rbp, r10, r15; hix458, lox457<- x443 * 0xee63bd076e8d9300
mov r15, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x6d8 ], rbp; spilling x458 to mem
mov byte [ rsp + 0x6e0 ], r8b; spilling byte x289 to mem
mulx r8, rbp, r15; hix450, lox449<- x443 * 0xcb8ac8495d187e8c
seto r15b;
mov [ rsp + 0x6e8 ], r8; spilling x450 to mem
mov r8, -0x2 ; moving imm to reg
inc r8; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r10, r13
seto r13b;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r8; loading flag
adox rdi, r10
mov r12, 0x32ea0103e01090bb ; moving imm to reg
mulx r8, r10, r12; hix452, lox451<- x443 * 0x32ea0103e01090bb
mov r12, [ rsp + 0x300 ]; load m64 x313 to register64
mov [ rsp + 0x6f0 ], rbp; spilling x449 to mem
seto bpl;
mov [ rsp + 0x6f8 ], r8; spilling x452 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r8; loading flag
adox r12, [ rsp + 0x670 ]
mov r11, [ rsp + 0x690 ]; load m64 x284 to register64
adox r11, [ rsp + 0x2e0 ]
adox rcx, [ rsp + 0x2d8 ]
mov r8, 0x155556ffff39ca9b ; moving imm to reg
mov [ rsp + 0x700 ], r10; spilling x451 to mem
mov byte [ rsp + 0x708 ], bpl; spilling byte x479 to mem
mulx rbp, r10, r8; hix446, lox445<- x443 * 0x155556ffff39ca9b
seto r8b;
mov [ rsp + 0x710 ], rbp; spilling x446 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rbp; loading flag
adox rbx, [ rsp + 0x628 ]
setc r9b;
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r14, [ rsp + 0x2d0 ]
mov r8, [ rsp + 0x688 ]; load m64 x239 to register64
seto bpl;
mov [ rsp + 0x718 ], r10; spilling x445 to mem
movzx r10, byte [ rsp + 0x6e0 ]; load byte memx289 to register64
mov [ rsp + 0x720 ], r14; spilling x336 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r14; loading flag
adox r8, [ rsp + 0x680 ]
mov r10, [ rsp + 0x6c0 ]; load m64 x349 to register64
seto r14b;
mov [ rsp + 0x728 ], rbx; spilling x368 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rbx; loading flag
adox r10, [ rsp + 0x6b8 ]
mov rbp, [ rsp + 0x6b0 ]; load m64 x347 to register64
adox rbp, [ rsp + 0x660 ]
adcx r8, [ rsp + 0x2f8 ]
movzx rbx, r14b;
mov [ rsp + 0x730 ], rbp; spilling x372 to mem
movzx rbp, byte [ rsp + 0x6a8 ]; load byte memx240 to register64
lea rbx, [ rbx + rbp ]; r64+m8
seto bpl;
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r14; loading flag
adox r12, [ rsp + 0x6a0 ]
adcx rbx, [ rsp + 0x390 ]
setc r15b;
clc;
movzx r9, r9b
adcx r9, r14; loading flag
adcx r12, [ rsp + 0x248 ]
movzx r9, bpl;
mov r14, [ rsp + 0x658 ]; load m64 x345 to register64
lea r9, [ r9 + r14 ]; r8/64 + m8
mov r14, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov byte [ rsp + 0x738 ], r15b; spilling byte x341 to mem
mulx r15, rbp, r14; hix456, lox455<- x443 * 0xcfcb5c6071bad3d2
seto r14b;
mov [ rsp + 0x740 ], r15; spilling x456 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r15; loading flag
adox rbp, [ rsp + 0x6d8 ]
seto r13b;
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r15; loading flag
adox r11, [ rsp + 0x698 ]
setc r14b;
clc;
adcx rdi, [ rsp + 0x3f0 ]
adox rcx, [ rsp + 0x728 ]
mov r15, 0x626e85bf7c18a0f0 ; moving imm to reg
mov byte [ rsp + 0x748 ], r13b; spilling byte x464 to mem
mov [ rsp + 0x750 ], rcx; spilling x385 to mem
mulx rcx, r13, r15; hix454, lox453<- x443 * 0x626e85bf7c18a0f0
mov rdx, 0x6efa1180a5fe67fd ; moving imm to reg
mov [ rsp + 0x758 ], rcx; spilling x454 to mem
mulx rcx, r15, rdi; hi_, lox544<- x526 * 0x6efa1180a5fe67fd
seto cl;
movzx rdx, byte [ rsp + 0x708 ]; load byte memx479 to register64
mov [ rsp + 0x760 ], r13; spilling x453 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rdx, r13; loading flag
adox r12, rbp
setc dl;
clc;
movzx rcx, cl
adcx rcx, r13; loading flag
adcx r10, [ rsp + 0x720 ]
mov rbp, 0xee63bd076e8d9300 ; moving imm to reg
xchg rdx, rbp; 0xee63bd076e8d9300, swapping with x527, which is currently in rdx
mulx r13, rcx, r15; hix559, lox558<- x544 * 0xee63bd076e8d9300
mov rdx, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x768 ], r13; spilling x559 to mem
mov [ rsp + 0x770 ], r12; spilling x480 to mem
mulx r12, r13, r15; hix549, lox548<- x544 * 0xfcedf2b4f9c0ecf6
seto dl;
mov [ rsp + 0x778 ], r12; spilling x549 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r12; loading flag
adox r11, [ rsp + 0x4d8 ]
adcx r8, [ rsp + 0x730 ]
adcx r9, rbx
mov rbx, [ rsp + 0x750 ]; load m64 x385 to register64
adox rbx, [ rsp + 0x5a8 ]
mov r14, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r15; x544, swapping with x481, which is currently in rdx
mov [ rsp + 0x780 ], r13; spilling x548 to mem
mulx r13, r12, r14; hix547, lox546<- x544 * 0x155556ffff39ca9b
adox r10, [ rsp + 0x5b0 ]
adox r8, [ rsp + 0x5e0 ]
mov r14, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x788 ], r13; spilling x547 to mem
mov [ rsp + 0x790 ], r12; spilling x546 to mem
mulx r12, r13, r14; hix551, lox550<- x544 * 0xcb8ac8495d187e8c
mov r14, [ rsp + 0x740 ]; load m64 x456 to register64
mov [ rsp + 0x798 ], r12; spilling x551 to mem
setc r12b;
mov [ rsp + 0x7a0 ], r13; spilling x550 to mem
movzx r13, byte [ rsp + 0x748 ]; load byte memx464 to register64
clc;
mov [ rsp + 0x7a8 ], r8; spilling x437 to mem
mov r8, -0x1 ; moving imm to reg
adcx r13, r8; loading flag
adcx r14, [ rsp + 0x760 ]
mov r13, 0xa13d118db8bfd2ab ; moving imm to reg
mov byte [ rsp + 0x7b0 ], r12b; spilling byte x392 to mem
mulx r12, r8, r13; hix561, lox560<- x544 * 0xa13d118db8bfd2ab
setc r13b;
clc;
mov [ rsp + 0x7b8 ], r10; spilling x435 to mem
mov r10, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r10; loading flag
adcx r11, r14
mov r15, [ rsp + 0x700 ]; load m64 x451 to register64
setc r14b;
clc;
movzx r13, r13b
adcx r13, r10; loading flag
adcx r15, [ rsp + 0x758 ]
setc r13b;
clc;
adcx rcx, r12
seto r12b;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r8, rdi
mov r8, [ rsp + 0x770 ]; load m64 x480 to register64
setc dil;
clc;
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx r8, [ rsp + 0x460 ]
adox rcx, r8
mov rbp, [ rsp + 0x6f0 ]; load m64 x449 to register64
setc r8b;
clc;
movzx r13, r13b
adcx r13, r10; loading flag
adcx rbp, [ rsp + 0x6f8 ]
setc r13b;
clc;
adcx rcx, [ rsp + 0x1d8 ]
mov r10, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, rcx; x627, swapping with x544, which is currently in rdx
mov byte [ rsp + 0x7c0 ], dil; spilling byte x563 to mem
mov [ rsp + 0x7c8 ], r11; spilling x482 to mem
mulx r11, rdi, r10; hi_, lox645<- x627 * 0x6efa1180a5fe67fd
seto r11b;
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r10; loading flag
adox rbx, r15
mov r14, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r14; 0x155556ffff39ca9b, swapping with x627, which is currently in rdx
mulx r10, r15, rdi; hix648, lox647<- x645 * 0x155556ffff39ca9b
mov rdx, [ rsp + 0x6e8 ]; load m64 x450 to register64
mov [ rsp + 0x7d0 ], r10; spilling x648 to mem
setc r10b;
clc;
mov [ rsp + 0x7d8 ], r15; spilling x647 to mem
mov r15, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, r15; loading flag
adcx rdx, [ rsp + 0x6d0 ]
mov r13, [ rsp + 0x718 ]; load m64 x445 to register64
adcx r13, [ rsp + 0x6c8 ]
setc r15b;
clc;
mov byte [ rsp + 0x7e0 ], r10b; spilling byte x628 to mem
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r10; loading flag
adcx r9, [ rsp + 0x620 ]
adox rbp, [ rsp + 0x7b8 ]
adox rdx, [ rsp + 0x7a8 ]
adox r13, r9
movzx r12, r15b;
mov r9, [ rsp + 0x710 ]; load m64 x446 to register64
lea r12, [ r12 + r9 ]; r8/64 + m8
mov r9, [ rsp + 0x468 ]; load m64 x513 to register64
seto r15b;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r10; loading flag
adox r9, [ rsp + 0x7c8 ]
adox rbx, [ rsp + 0x4c0 ]
mov r8, 0xcfcb5c6071bad3d2 ; moving imm to reg
xchg rdx, r8; 0xcfcb5c6071bad3d2, swapping with x488, which is currently in rdx
mov [ rsp + 0x7e8 ], rbx; spilling x532 to mem
mulx rbx, r10, rcx; hix557, lox556<- x544 * 0xcfcb5c6071bad3d2
mov rdx, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x7f0 ], r12; spilling x475 to mem
mov byte [ rsp + 0x7f8 ], r15b; spilling byte x491 to mem
mulx r15, r12, rdi; hix652, lox651<- x645 * 0xcb8ac8495d187e8c
mov rdx, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x800 ], r15; spilling x652 to mem
mov [ rsp + 0x808 ], r12; spilling x651 to mem
mulx r12, r15, rdi; hix660, lox659<- x645 * 0xee63bd076e8d9300
adox rbp, [ rsp + 0x4b8 ]
adox r8, [ rsp + 0x4e0 ]
mov rdx, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x810 ], r8; spilling x536 to mem
mov [ rsp + 0x818 ], rbp; spilling x534 to mem
mulx rbp, r8, rdi; hix650, lox649<- x645 * 0xfcedf2b4f9c0ecf6
mov rdx, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x820 ], rbp; spilling x650 to mem
mov [ rsp + 0x828 ], r8; spilling x649 to mem
mulx r8, rbp, rdi; hix662, lox661<- x645 * 0xa13d118db8bfd2ab
setc dl;
clc;
adcx rbp, r14
movzx rbp, byte [ rsp + 0x7b0 ];
movzx r14, byte [ rsp + 0x738 ]; load byte memx341 to register64
lea rbp, [ rbp + r14 ]; r64+m8
seto r14b;
mov [ rsp + 0x830 ], r12; spilling x660 to mem
movzx r12, byte [ rsp + 0x7c0 ]; load byte memx563 to register64
mov [ rsp + 0x838 ], r15; spilling x659 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
adox r12, r15; loading flag
adox r10, [ rsp + 0x768 ]
seto r12b;
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r15; loading flag
adox r13, [ rsp + 0x538 ]
mov r14, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, rcx; x544, swapping with x440, which is currently in rdx
mov [ rsp + 0x840 ], r13; spilling x538 to mem
mulx r13, r15, r14; hix553, lox552<- x544 * 0x32ea0103e01090bb
setc r14b;
clc;
mov [ rsp + 0x848 ], r8; spilling x662 to mem
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r8; loading flag
adcx rbp, [ rsp + 0x648 ]
mov rcx, 0x626e85bf7c18a0f0 ; moving imm to reg
mov byte [ rsp + 0x850 ], r14b; spilling byte x679 to mem
mulx r14, r8, rcx; hix555, lox554<- x544 * 0x626e85bf7c18a0f0
seto dl;
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rcx; loading flag
adox r9, r10
seto r11b;
movzx r10, byte [ rsp + 0x7e0 ]; load byte memx628 to register64
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
adox r10, rcx; loading flag
adox r9, [ rsp + 0x250 ]
mov r10, 0xcfcb5c6071bad3d2 ; moving imm to reg
xchg rdx, rdi; x645, swapping with x539, which is currently in rdx
mov [ rsp + 0x858 ], r9; spilling x629 to mem
mulx r9, rcx, r10; hix658, lox657<- x645 * 0xcfcb5c6071bad3d2
seto r10b;
mov [ rsp + 0x860 ], r9; spilling x658 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r9; loading flag
adox rbx, r8
adox r15, r14
setc r12b;
movzx r8, byte [ rsp + 0x7f8 ]; load byte memx491 to register64
clc;
adcx r8, r9; loading flag
adcx rbp, [ rsp + 0x7f0 ]
adox r13, [ rsp + 0x7a0 ]
mov r8, [ rsp + 0x838 ]; load m64 x659 to register64
setc r14b;
clc;
adcx r8, [ rsp + 0x848 ]
seto r9b;
mov byte [ rsp + 0x868 ], r10b; spilling byte x630 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r10; loading flag
adox rbp, [ rsp + 0x528 ]
movzx rdi, byte [ rsp + 0x530 ];
mov r10, [ rsp + 0x490 ]; load m64 x496 to register64
lea rdi, [ rdi + r10 ]; r8/64 + m8
adcx rcx, [ rsp + 0x830 ]
movzx r10, r14b;
movzx r12, r12b
lea r10, [ r10 + r12 ]
mov r12, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x870 ], rbp; spilling x540 to mem
mulx rbp, r14, r12; hix656, lox655<- x645 * 0x626e85bf7c18a0f0
seto r12b;
mov [ rsp + 0x878 ], rbp; spilling x656 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r11, r11b
adox r11, rbp; loading flag
adox rbx, [ rsp + 0x7e8 ]
adcx r14, [ rsp + 0x860 ]
setc r11b;
movzx rbp, byte [ rsp + 0x850 ]; load byte memx679 to register64
clc;
mov [ rsp + 0x880 ], r14; spilling x667 to mem
mov r14, -0x1 ; moving imm to reg
adcx rbp, r14; loading flag
adcx r8, [ rsp + 0x858 ]
setc bpl;
clc;
adcx r8, [ rsp + 0x220 ]
adox r15, [ rsp + 0x818 ]
mov r14, [ rsp + 0x798 ]; load m64 x551 to register64
mov byte [ rsp + 0x888 ], r11b; spilling byte x668 to mem
setc r11b;
clc;
mov [ rsp + 0x890 ], r15; spilling x585 to mem
mov r15, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r15; loading flag
adcx r14, [ rsp + 0x780 ]
mov r9, [ rsp + 0x790 ]; load m64 x546 to register64
adcx r9, [ rsp + 0x778 ]
adox r13, [ rsp + 0x810 ]
mov r15, [ rsp + 0x788 ];
mov byte [ rsp + 0x898 ], r11b; spilling byte x729 to mem
mov r11, 0x0 ; moving imm to reg
adcx r15, r11
adox r14, [ rsp + 0x840 ]
movzx r11, byte [ rsp + 0x868 ]; load byte memx630 to register64
clc;
mov [ rsp + 0x8a0 ], r14; spilling x589 to mem
mov r14, -0x1 ; moving imm to reg
adcx r11, r14; loading flag
adcx rbx, [ rsp + 0x290 ]
seto r11b;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, r14; loading flag
adox r10, rdi
seto r12b;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, rdi; loading flag
adox rbx, rcx
setc cl;
clc;
movzx r11, r11b
adcx r11, rdi; loading flag
adcx r9, [ rsp + 0x870 ]
adcx r15, r10
movzx rbp, r12b;
adcx rbp, r14
mov r11, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r8; x728, swapping with x645, which is currently in rdx
mulx r12, r10, r11; hi_, lox746<- x728 * 0x6efa1180a5fe67fd
mov r12, 0xee63bd076e8d9300 ; moving imm to reg
xchg rdx, r12; 0xee63bd076e8d9300, swapping with x728, which is currently in rdx
mulx rdi, r14, r10; hix761, lox760<- x746 * 0xee63bd076e8d9300
mov rdx, [ rsp + 0x890 ]; load m64 x585 to register64
clc;
mov r11, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, r11; loading flag
adcx rdx, [ rsp + 0x278 ]
adcx r13, [ rsp + 0x288 ]
mov rcx, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
xchg rdx, rcx; 0xfcedf2b4f9c0ecf6, swapping with x633, which is currently in rdx
mov [ rsp + 0x8a8 ], rbp; spilling x595 to mem
mulx rbp, r11, r10; hix751, lox750<- x746 * 0xfcedf2b4f9c0ecf6
mov rdx, [ rsp + 0x8a0 ]; load m64 x589 to register64
adcx rdx, [ rsp + 0x350 ]
mov [ rsp + 0x8b0 ], rbp; spilling x751 to mem
mov rbp, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, rbp; 0x32ea0103e01090bb, swapping with x637, which is currently in rdx
mov [ rsp + 0x8b8 ], r11; spilling x750 to mem
mov [ rsp + 0x8c0 ], r15; spilling x593 to mem
mulx r15, r11, r8; hix654, lox653<- x645 * 0x32ea0103e01090bb
adcx r9, [ rsp + 0x4d0 ]
seto r8b;
movzx rdx, byte [ rsp + 0x888 ]; load byte memx668 to register64
mov [ rsp + 0x8c8 ], r9; spilling x639 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox rdx, r9; loading flag
adox r11, [ rsp + 0x878 ]
setc dl;
clc;
movzx r8, r8b
adcx r8, r9; loading flag
adcx rcx, [ rsp + 0x880 ]
mov r8, 0xcb8ac8495d187e8c ; moving imm to reg
xchg rdx, r10; x746, swapping with x640, which is currently in rdx
mov byte [ rsp + 0x8d0 ], r10b; spilling byte x640 to mem
mulx r10, r9, r8; hix753, lox752<- x746 * 0xcb8ac8495d187e8c
adox r15, [ rsp + 0x808 ]
mov r8, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x8d8 ], r10; spilling x753 to mem
mov [ rsp + 0x8e0 ], r9; spilling x752 to mem
mulx r9, r10, r8; hix763, lox762<- x746 * 0xa13d118db8bfd2ab
adcx r11, r13
seto r13b;
movzx r8, byte [ rsp + 0x898 ]; load byte memx729 to register64
mov [ rsp + 0x8e8 ], r10; spilling x762 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
adox r8, r10; loading flag
adox rbx, [ rsp + 0x238 ]
seto r8b;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r14, r9
adcx r15, rbp
mov rbp, 0xcfcb5c6071bad3d2 ; moving imm to reg
mulx r10, r9, rbp; hix759, lox758<- x746 * 0xcfcb5c6071bad3d2
mov rbp, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x8f0 ], r14; spilling x764 to mem
mov [ rsp + 0x8f8 ], rbx; spilling x730 to mem
mulx rbx, r14, rbp; hix757, lox756<- x746 * 0x626e85bf7c18a0f0
adox r9, rdi
adox r14, r10
mov rdi, 0x32ea0103e01090bb ; moving imm to reg
mulx rbp, r10, rdi; hix755, lox754<- x746 * 0x32ea0103e01090bb
adox r10, rbx
seto bl;
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, rdi; loading flag
adox rcx, [ rsp + 0x2f0 ]
mov r8, [ rsp + 0x800 ]; load m64 x652 to register64
setc dil;
clc;
mov [ rsp + 0x900 ], rbp; spilling x755 to mem
mov rbp, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rbp; loading flag
adcx r8, [ rsp + 0x828 ]
adox r11, [ rsp + 0x2e8 ]
adox r15, [ rsp + 0x348 ]
setc r13b;
clc;
movzx rdi, dil
adcx rdi, rbp; loading flag
adcx r8, [ rsp + 0x8c8 ]
adox r8, [ rsp + 0x340 ]
setc dil;
clc;
adcx r12, [ rsp + 0x8e8 ]
mov r12, [ rsp + 0x8f8 ]; load m64 x730 to register64
adcx r12, [ rsp + 0x8f0 ]
mov rbp, [ rsp + 0x8c0 ]; load m64 x593 to register64
mov [ rsp + 0x908 ], r8; spilling x738 to mem
setc r8b;
mov [ rsp + 0x910 ], r12; spilling x781 to mem
movzx r12, byte [ rsp + 0x8d0 ]; load byte memx640 to register64
clc;
mov byte [ rsp + 0x918 ], bl; spilling byte x771 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r12, rbx; loading flag
adcx rbp, [ rsp + 0x518 ]
mov r12, [ rsp + 0x820 ]; load m64 x650 to register64
seto bl;
mov [ rsp + 0x920 ], r10; spilling x770 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, r10; loading flag
adox r12, [ rsp + 0x7d8 ]
mov r13, [ rsp + 0x7d0 ];
mov r10, 0x0 ; moving imm to reg
adox r13, r10
dec r10; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx rdi, dil
adox rdi, r10; loading flag
adox rbp, r12
seto dil;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r12; loading flag
adox rcx, r9
adox r14, r11
mov r9, [ rsp + 0x8a8 ]; load m64 x595 to register64
adcx r9, [ rsp + 0x5c0 ]
adox r15, [ rsp + 0x920 ]
mov r11, [ rsp + 0x900 ]; load m64 x755 to register64
setc r8b;
movzx r10, byte [ rsp + 0x918 ]; load byte memx771 to register64
clc;
adcx r10, r12; loading flag
adcx r11, [ rsp + 0x8e0 ]
seto r10b;
setc r12b;
mov [ rsp + 0x928 ], r15; spilling x787 to mem
mov r15, [ rsp + 0x910 ]; load m64 x781 to register64
mov [ rsp + 0x930 ], r14; spilling x785 to mem
mov r14, 0xa13d118db8bfd2ab ; moving imm to reg
mov byte [ rsp + 0x938 ], r8b; spilling byte x644 to mem
mov r8, r15;
sub r8, r14
mov r14, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x940 ], r8; spilling x798 to mem
mov r8, rcx;
sbb r8, r14
mov r14, -0x1 ; moving imm to reg
inc r14; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r14, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r14; loading flag
adox r11, [ rsp + 0x908 ]
seto r10b;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, r14; loading flag
adox r9, r13
seto r13b;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rdi; loading flag
adox rbp, [ rsp + 0x360 ]
adox r9, [ rsp + 0x448 ]
movzx rbx, r13b;
movzx r14, byte [ rsp + 0x938 ]; load byte memx644 to register64
lea rbx, [ rbx + r14 ]; r64+m8
adox rbx, [ rsp + 0x450 ]
mov r14, 0x155556ffff39ca9b ; moving imm to reg
mulx rdi, r13, r14; hix749, lox748<- x746 * 0x155556ffff39ca9b
mov rdx, [ rsp + 0x8d8 ]; load m64 x753 to register64
setc r14b;
clc;
mov [ rsp + 0x948 ], r8; spilling x800 to mem
mov r8, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r8; loading flag
adcx rdx, [ rsp + 0x8b8 ]
seto r12b;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r8; loading flag
adox rbp, rdx
adcx r13, [ rsp + 0x8b0 ]
adox r13, r9
mov r10, 0x0 ; moving imm to reg
adcx rdi, r10
adox rdi, rbx
seto r9b;
add r8b, r14b; load to CF<-x801
mov r8, [ rsp + 0x930 ]; load m64 x785 to register64
mov rbx, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov rdx, r8;
sbb rdx, rbx
mov r14, [ rsp + 0x928 ]; load m64 x787 to register64
mov r10, 0x626e85bf7c18a0f0 ; moving imm to reg
mov rbx, r14;
sbb rbx, r10
mov r10, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x950 ], rbx; spilling x804 to mem
mov rbx, r11;
sbb rbx, r10
mov r10, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x958 ], rbx; spilling x806 to mem
mov rbx, rbp;
sbb rbx, r10
mov r10, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x960 ], rbx; spilling x808 to mem
mov rbx, r13;
sbb rbx, r10
mov r10, 0x155556ffff39ca9b ; moving imm to reg
mov [ rsp + 0x968 ], rdx; spilling x802 to mem
mov rdx, rdi;
sbb rdx, r10
movzx r10, r9b;
movzx r12, r12b
lea r10, [ r10 + r12 ]
mov r12, 0x0 ; moving imm to reg
sbb r10, r12
cmovc rbx, r13; if CF, x822<- x793 (nzVar)
mov r10, [ rsp + 0x968 ];
cmovc r10, r8; if CF, x818<- x785 (nzVar)
cmovc rdx, rdi; if CF, x823<- x795 (nzVar)
mov r8, [ rsp + 0x948 ];
cmovc r8, rcx; if CF, x817<- x783 (nzVar)
mov rcx, [ rsp + 0x960 ];
cmovc rcx, rbp; if CF, x821<- x791 (nzVar)
mov rbp, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ rbp + 0x28 ], rcx; out1[5] = x821
mov r13, [ rsp + 0x940 ];
cmovc r13, r15; if CF, x816<- x781 (nzVar)
mov [ rbp + 0x10 ], r10; out1[2] = x818
mov [ rbp + 0x0 ], r13; out1[0] = x816
mov r15, [ rsp + 0x950 ];
cmovc r15, r14; if CF, x819<- x787 (nzVar)
mov [ rbp + 0x18 ], r15; out1[3] = x819
mov r14, [ rsp + 0x958 ];
cmovc r14, r11; if CF, x820<- x789 (nzVar)
mov [ rbp + 0x20 ], r14; out1[4] = x820
mov [ rbp + 0x8 ], r8; out1[1] = x817
mov [ rbp + 0x38 ], rdx; out1[7] = x823
mov [ rbp + 0x30 ], rbx; out1[6] = x822
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
add rsp, 2544
ret
; cpu AMD Ryzen 7 PRO 7840U w/ Radeon 780M Graphics
; ratio 1.8395
; seed 0001775468955356 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; cyclegoal; 10000
; using counter; RDTSCP
; framePointer omit
; memoryConstraints none
; time needed: 1758281 ms on 5000 evaluations.
; Time spent for assembling and measuring (initial batch_size=9, initial num_batches=31): 19564 ms
; number of used evaluations: 5000
; Ratio (time for assembling + measure)/(total runtime for 5000 evals): 0.011126776664253324
; number reverted permutation / tried permutation: 1120 / 2434 =46.015%
; number reverted decision / tried decision: 1144 / 2565 =44.600%