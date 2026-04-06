SECTION .text
	GLOBAL fiat_bls24_509_p_square
fiat_bls24_509_p_square:
sub rsp, 2528
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mulx r10, rax, [ rsi + 0x28 ]; hix504, lox503<- arg1[5] * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mulx rcx, r11, [ rsi + 0x10 ]; hix102, lox101<- arg1[1] * arg1[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mulx r9, r8, [ rsi + 0x8 ]; hix92, lox91<- arg1[1] * arg1[7]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp - 0x80 ], rbx; spilling calSv-rbx to mem
mov [ rsp - 0x78 ], rbp; spilling calSv-rbp to mem
mulx rbp, rbx, [ rsi + 0x38 ]; hix712, lox711<- arg1[7] * arg1[0]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp - 0x70 ], r12; spilling calSv-r12 to mem
mov [ rsp - 0x68 ], r13; spilling calSv-r13 to mem
mulx r13, r12, rdx; hix401, lox400<- arg1[4]^2
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x60 ], r14; spilling calSv-r14 to mem
mov [ rsp - 0x58 ], r15; spilling calSv-r15 to mem
mulx r15, r14, rdx; hix302, lox301<- arg1[3]^2
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp - 0x50 ], rdi; spilling out1 to mem
mov [ rsp - 0x48 ], rbx; spilling x711 to mem
mulx rbx, rdi, [ rsi + 0x28 ]; hix498, lox497<- arg1[5] * arg1[6]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp - 0x40 ], r13; spilling x401 to mem
mov [ rsp - 0x38 ], r9; spilling x92 to mem
mulx r9, r13, [ rsi + 0x38 ]; hix706, lox705<- arg1[7] * arg1[3]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp - 0x30 ], rbx; spilling x498 to mem
mov [ rsp - 0x28 ], r15; spilling x302 to mem
mulx r15, rbx, [ rsi + 0x18 ]; hix304, lox303<- arg1[3] * arg1[2]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp - 0x20 ], r8; spilling x91 to mem
mov [ rsp - 0x18 ], rdi; spilling x497 to mem
mulx rdi, r8, [ rsi + 0x20 ]; hix399, lox398<- arg1[4] * arg1[5]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp - 0x10 ], rdi; spilling x399 to mem
mov [ rsp - 0x8 ], r8; spilling x398 to mem
mulx r8, rdi, [ rsi + 0x8 ]; hix94, lox93<- arg1[1] * arg1[6]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x0 ], r8; spilling x94 to mem
mov [ rsp + 0x8 ], r10; spilling x504 to mem
mulx r10, r8, [ rsi + 0x0 ]; hix409, lox408<- arg1[4] * arg1[0]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x10 ], r8; spilling x408 to mem
mov [ rsp + 0x18 ], rdi; spilling x93 to mem
mulx rdi, r8, [ rsi + 0x30 ]; hix611, lox610<- arg1[6] * arg1[0]
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x20 ], r8; spilling x610 to mem
mov [ rsp + 0x28 ], r9; spilling x706 to mem
mulx r9, r8, [ rsi + 0x20 ]; hix502, lox501<- arg1[5] * arg1[4]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x30 ], r9; spilling x502 to mem
mov [ rsp + 0x38 ], r8; spilling x501 to mem
mulx r8, r9, [ rsi + 0x0 ]; hix106, lox105<- arg1[1] * arg1[0]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x40 ], r9; spilling x105 to mem
mov [ rsp + 0x48 ], r13; spilling x705 to mem
mulx r13, r9, [ rsi + 0x28 ]; hix601, lox600<- arg1[6] * arg1[5]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x50 ], r12; spilling x400 to mem
mov [ rsp + 0x58 ], r13; spilling x601 to mem
mulx r13, r12, [ rsi + 0x38 ]; hix10, lox9<- arg1[0] * arg1[7]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x60 ], r13; spilling x10 to mem
mov [ rsp + 0x68 ], r12; spilling x9 to mem
mulx r12, r13, [ rsi + 0x20 ]; hix704, lox703<- arg1[7] * arg1[4]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x70 ], r12; spilling x704 to mem
mov [ rsp + 0x78 ], r13; spilling x703 to mem
mulx r13, r12, [ rsi + 0x30 ]; hix597, lox596<- arg1[6] * arg1[7]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x80 ], r13; spilling x597 to mem
mov [ rsp + 0x88 ], r12; spilling x596 to mem
mulx r12, r13, [ rsi + 0x20 ]; hix16, lox15<- arg1[0] * arg1[4]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x90 ], r9; spilling x600 to mem
mov [ rsp + 0x98 ], rcx; spilling x102 to mem
mulx rcx, r9, [ rsi + 0x10 ]; hix207, lox206<- arg1[2] * arg1[0]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xa0 ], r9; spilling x206 to mem
mov [ rsp + 0xa8 ], r11; spilling x101 to mem
mulx r11, r9, rdx; hix698, lox697<- arg1[7]^2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xb0 ], r11; spilling x698 to mem
mov [ rsp + 0xb8 ], r9; spilling x697 to mem
mulx r9, r11, [ rsi + 0x20 ]; hix405, lox404<- arg1[4] * arg1[2]
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0xc0 ], r9; spilling x405 to mem
mov [ rsp + 0xc8 ], r8; spilling x106 to mem
mulx r8, r9, [ rsi + 0x8 ]; hix710, lox709<- arg1[7] * arg1[1]
add r9, rbp; could be done better, if r0 has been u8 as well
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0xd0 ], r9; spilling x713 to mem
mulx r9, rbp, [ rsi + 0x8 ]; hix508, lox507<- arg1[5] * arg1[1]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xd8 ], r12; spilling x16 to mem
mov [ rsp + 0xe0 ], r13; spilling x15 to mem
mulx r13, r12, rdx; hix24, lox23<- arg1[0]^2
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0xe8 ], r11; spilling x404 to mem
mov [ rsp + 0xf0 ], rax; spilling x503 to mem
mulx rax, r11, [ rsi + 0x28 ]; hix510, lox509<- arg1[5] * arg1[0]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0xf8 ], r11; spilling x509 to mem
mov [ rsp + 0x100 ], r9; spilling x508 to mem
mulx r9, r11, [ rsi + 0x38 ]; hix708, lox707<- arg1[7] * arg1[2]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x108 ], r9; spilling x708 to mem
mov [ rsp + 0x110 ], r10; spilling x409 to mem
mulx r10, r9, [ rsi + 0x20 ]; hix98, lox97<- arg1[1] * arg1[4]
mov rdx, -0x2 ; moving imm to reg
inc rdx; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, rax
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x118 ], rbp; spilling x511 to mem
mulx rbp, rax, [ rsi + 0x20 ]; hix403, lox402<- arg1[4] * arg1[3]
mov rdx, 0x6efa1180a5fe67fd ; moving imm to reg
mov [ rsp + 0x120 ], r10; spilling x98 to mem
mov [ rsp + 0x128 ], rbp; spilling x403 to mem
mulx rbp, r10, r12; hi_, lox40<- x23 * 0x6efa1180a5fe67fd
mov rdx, [ rsi + 0x38 ]; arg1[7] to rdx
mov [ rsp + 0x130 ], rax; spilling x402 to mem
mulx rax, rbp, [ rsi + 0x30 ]; hix700, lox699<- arg1[7] * arg1[6]
mov rdx, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x138 ], rax; spilling x700 to mem
mov [ rsp + 0x140 ], rbp; spilling x699 to mem
mulx rbp, rax, r10; hix51, lox50<- x40 * 0x626e85bf7c18a0f0
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x148 ], rbp; spilling x51 to mem
mov [ rsp + 0x150 ], rax; spilling x50 to mem
mulx rax, rbp, [ rsi + 0x8 ]; hix306, lox305<- arg1[3] * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x158 ], r9; spilling x97 to mem
mov [ rsp + 0x160 ], rdi; spilling x611 to mem
mulx rdi, r9, [ rsi + 0x0 ]; hix308, lox307<- arg1[3] * arg1[0]
mov rdx, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x168 ], r9; spilling x307 to mem
mov [ rsp + 0x170 ], r14; spilling x301 to mem
mulx r14, r9, r10; hix57, lox56<- x40 * 0xa13d118db8bfd2ab
adcx r11, r8
mov r8, 0x155556ffff39ca9b ; moving imm to reg
mov rdx, r10; x40 to rdx
mov [ rsp + 0x178 ], r11; spilling x715 to mem
mulx r11, r10, r8; hix43, lox42<- x40 * 0x155556ffff39ca9b
mov r8, rdx; preserving value of x40 into a new reg
mov rdx, [ rsi + 0x8 ]; saving arg1[1] in rdx.
mov [ rsp + 0x180 ], r11; spilling x43 to mem
mov [ rsp + 0x188 ], r10; spilling x42 to mem
mulx r10, r11, [ rsi + 0x10 ]; hix205, lox204<- arg1[2] * arg1[1]
setc dl;
clc;
adcx r11, rcx
mov rcx, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
xchg rdx, r8; x40, swapping with x716, which is currently in rdx
mov [ rsp + 0x190 ], r11; spilling x208 to mem
mov byte [ rsp + 0x198 ], r8b; spilling byte x716 to mem
mulx r8, r11, rcx; hix45, lox44<- x40 * 0xfcedf2b4f9c0ecf6
setc cl;
clc;
adcx rbp, rdi
mov rdi, rdx; preserving value of x40 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mov [ rsp + 0x1a0 ], rbp; spilling x309 to mem
mov [ rsp + 0x1a8 ], r8; spilling x45 to mem
mulx r8, rbp, [ rsi + 0x8 ]; hix22, lox21<- arg1[0] * arg1[1]
seto dl;
mov [ rsp + 0x1b0 ], r11; spilling x44 to mem
mov r11, -0x2 ; moving imm to reg
inc r11; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, r13
adcx rbx, rax
mov r13b, dl; preserving value of x512 into a new reg
mov rdx, [ rsi + 0x0 ]; saving arg1[0] in rdx.
mulx r11, rax, [ rsi + 0x10 ]; hix20, lox19<- arg1[0] * arg1[2]
adox rax, r8
adcx r15, [ rsp + 0x170 ]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x1b8 ], r15; spilling x313 to mem
mulx r15, r8, [ rsi + 0x18 ]; hix18, lox17<- arg1[0] * arg1[3]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x1c0 ], rbx; spilling x311 to mem
mov [ rsp + 0x1c8 ], rax; spilling x27 to mem
mulx rax, rbx, [ rsi + 0x30 ]; hix609, lox608<- arg1[6] * arg1[1]
mov rdx, [ rsi + 0x8 ]; arg1[1] to rdx
mov [ rsp + 0x1d0 ], rbp; spilling x25 to mem
mov [ rsp + 0x1d8 ], r14; spilling x57 to mem
mulx r14, rbp, rdx; hix104, lox103<- arg1[1]^2
adox r8, r11
setc dl;
clc;
adcx rbx, [ rsp + 0x160 ]
mov r11b, dl; preserving value of x314 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x1e0 ], rbx; spilling x612 to mem
mov [ rsp + 0x1e8 ], r8; spilling x29 to mem
mulx r8, rbx, [ rsi + 0x10 ]; hix506, lox505<- arg1[5] * arg1[2]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov byte [ rsp + 0x1f0 ], r11b; spilling byte x314 to mem
mov [ rsp + 0x1f8 ], r14; spilling x104 to mem
mulx r14, r11, [ rsi + 0x30 ]; hix607, lox606<- arg1[6] * arg1[2]
mov rdx, [ rsi + 0x0 ]; arg1[0] to rdx
mov [ rsp + 0x200 ], r9; spilling x56 to mem
mov [ rsp + 0x208 ], rbp; spilling x103 to mem
mulx rbp, r9, [ rsi + 0x28 ]; hix14, lox13<- arg1[0] * arg1[5]
mov rdx, [ rsi + 0x20 ]; arg1[4] to rdx
mov [ rsp + 0x210 ], rbp; spilling x14 to mem
mov [ rsp + 0x218 ], r9; spilling x13 to mem
mulx r9, rbp, [ rsi + 0x8 ]; hix407, lox406<- arg1[4] * arg1[1]
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x220 ], r15; spilling x18 to mem
mov [ rsp + 0x228 ], r10; spilling x205 to mem
mulx r10, r15, [ rsi + 0x30 ]; hix605, lox604<- arg1[6] * arg1[3]
seto dl;
mov [ rsp + 0x230 ], r10; spilling x605 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rbp, [ rsp + 0x110 ]
adcx r11, rax
adcx r15, r14
seto al;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r14; loading flag
adox rbx, [ rsp + 0x100 ]
mov r13b, dl; preserving value of x30 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mulx r14, r10, rdx; hix203, lox202<- arg1[2]^2
adox r8, [ rsp + 0xf0 ]
seto dl;
mov [ rsp + 0x238 ], r15; spilling x616 to mem
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx rax, al
adox rax, r15; loading flag
adox r9, [ rsp + 0xe8 ]
mov al, dl; preserving value of x516 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x240 ], r11; spilling x614 to mem
mulx r11, r15, [ rsi + 0x30 ]; hix603, lox602<- arg1[6] * arg1[4]
seto dl;
mov [ rsp + 0x248 ], r8; spilling x515 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r8; loading flag
adox r10, [ rsp + 0x228 ]
mov rcx, [ rsp + 0x220 ]; load m64 x18 to register64
setc r8b;
clc;
mov [ rsp + 0x250 ], rbx; spilling x513 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r13, r13b
adcx r13, rbx; loading flag
adcx rcx, [ rsp + 0xe0 ]
mov r13, [ rsp + 0x218 ]; load m64 x13 to register64
adcx r13, [ rsp + 0xd8 ]
seto bl;
mov [ rsp + 0x258 ], r9; spilling x412 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r8, r8b
adox r8, r9; loading flag
adox r15, [ rsp + 0x230 ]
mov r8b, dl; preserving value of x413 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x260 ], r15; spilling x618 to mem
mulx r15, r9, [ rsi + 0x0 ]; hix12, lox11<- arg1[0] * arg1[6]
adcx r9, [ rsp + 0x210 ]
mov rdx, [ rsp + 0xc8 ]; load m64 x106 to register64
mov [ rsp + 0x268 ], rbp; spilling x410 to mem
setc bpl;
clc;
adcx rdx, [ rsp + 0x208 ]
mov [ rsp + 0x270 ], r10; spilling x210 to mem
setc r10b;
clc;
adcx r12, [ rsp + 0x200 ]
mov r12, rdx; preserving value of x107 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x278 ], r9; spilling x35 to mem
mov [ rsp + 0x280 ], r13; spilling x33 to mem
mulx r13, r9, [ rsi + 0x8 ]; hix100, lox99<- arg1[1] * arg1[3]
mov rdx, [ rsp + 0x1f8 ]; load m64 x104 to register64
mov [ rsp + 0x288 ], r12; spilling x107 to mem
seto r12b;
mov [ rsp + 0x290 ], rcx; spilling x31 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, rcx; loading flag
adox rdx, [ rsp + 0xa8 ]
adox r9, [ rsp + 0x98 ]
adox r13, [ rsp + 0x158 ]
mov r10, rdx; preserving value of x109 into a new reg
mov rdx, [ rsi + 0x30 ]; saving arg1[6] in rdx.
mov [ rsp + 0x298 ], r13; spilling x113 to mem
mulx r13, rcx, rdx; hix599, lox598<- arg1[6]^2
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x2a0 ], r13; spilling x599 to mem
mov [ rsp + 0x2a8 ], r9; spilling x111 to mem
mulx r9, r13, [ rsi + 0x28 ]; hix197, lox196<- arg1[2] * arg1[5]
setc dl;
clc;
mov [ rsp + 0x2b0 ], r10; spilling x109 to mem
mov r10, -0x1 ; moving imm to reg
movzx r12, r12b
adcx r12, r10; loading flag
adcx r11, [ rsp + 0x90 ]
setc r12b;
clc;
movzx rbp, bpl
adcx rbp, r10; loading flag
adcx r15, [ rsp + 0x68 ]
mov rbp, 0xcfcb5c6071bad3d2 ; moving imm to reg
xchg rdx, rdi; x40, swapping with x74, which is currently in rdx
mov [ rsp + 0x2b8 ], r11; spilling x620 to mem
mulx r11, r10, rbp; hix53, lox52<- x40 * 0xcfcb5c6071bad3d2
mov rbp, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x2c0 ], r15; spilling x37 to mem
mov [ rsp + 0x2c8 ], r9; spilling x197 to mem
mulx r9, r15, rbp; hix55, lox54<- x40 * 0xee63bd076e8d9300
seto bpl;
mov byte [ rsp + 0x2d0 ], al; spilling byte x516 to mem
mov rax, -0x2 ; moving imm to reg
inc rax; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r15, [ rsp + 0x1d8 ]
seto al;
mov byte [ rsp + 0x2d8 ], bpl; spilling byte x114 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r12, r12b
adox r12, rbp; loading flag
adox rcx, [ rsp + 0x58 ]
mov r12, rdx; preserving value of x40 into a new reg
mov rdx, [ rsi + 0x10 ]; saving arg1[2] in rdx.
mov [ rsp + 0x2e0 ], rcx; spilling x622 to mem
mulx rcx, rbp, [ rsi + 0x18 ]; hix201, lox200<- arg1[2] * arg1[3]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov byte [ rsp + 0x2e8 ], r8b; spilling byte x413 to mem
mov [ rsp + 0x2f0 ], r11; spilling x53 to mem
mulx r11, r8, [ rsi + 0x20 ]; hix199, lox198<- arg1[2] * arg1[4]
mov rdx, [ rsi + 0x10 ]; arg1[2] to rdx
mov [ rsp + 0x2f8 ], r13; spilling x196 to mem
mov [ rsp + 0x300 ], r11; spilling x199 to mem
mulx r11, r13, [ rsi + 0x30 ]; hix195, lox194<- arg1[2] * arg1[6]
setc dl;
clc;
mov [ rsp + 0x308 ], r11; spilling x195 to mem
mov r11, -0x1 ; moving imm to reg
movzx rdi, dil
adcx rdi, r11; loading flag
adcx r15, [ rsp + 0x1d0 ]
mov dil, dl; preserving value of x38 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x310 ], r13; spilling x194 to mem
mulx r13, r11, [ rsi + 0x8 ]; hix96, lox95<- arg1[1] * arg1[5]
seto dl;
mov byte [ rsp + 0x318 ], dil; spilling byte x38 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbx, bl
adox rbx, rdi; loading flag
adox r14, rbp
setc bl;
clc;
movzx rax, al
adcx rax, rdi; loading flag
adcx r9, r10
adox r8, rcx
mov r10, [ rsp + 0x300 ]; load m64 x199 to register64
adox r10, [ rsp + 0x2f8 ]
seto al;
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rbp; loading flag
adox r9, [ rsp + 0x1c8 ]
mov rcx, [ rsp + 0x2f0 ]; load m64 x53 to register64
adcx rcx, [ rsp + 0x150 ]
mov rbx, [ rsp + 0x130 ]; load m64 x402 to register64
setc dil;
movzx rbp, byte [ rsp + 0x2e8 ]; load byte memx413 to register64
clc;
mov byte [ rsp + 0x320 ], dl; spilling byte x623 to mem
mov rdx, -0x1 ; moving imm to reg
adcx rbp, rdx; loading flag
adcx rbx, [ rsp + 0xc0 ]
mov rbp, [ rsp + 0x50 ]; load m64 x400 to register64
adcx rbp, [ rsp + 0x128 ]
mov rdx, [ rsp + 0x108 ]; load m64 x708 to register64
mov [ rsp + 0x328 ], rbp; spilling x416 to mem
seto bpl;
mov [ rsp + 0x330 ], rbx; spilling x414 to mem
movzx rbx, byte [ rsp + 0x198 ]; load byte memx716 to register64
mov [ rsp + 0x338 ], r10; spilling x216 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox rbx, r10; loading flag
adox rdx, [ rsp + 0x48 ]
mov rbx, rdx; preserving value of x717 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov [ rsp + 0x340 ], r8; spilling x214 to mem
mulx r8, r10, rdx; hix500, lox499<- arg1[5]^2
mov rdx, [ rsi + 0x28 ]; arg1[5] to rdx
mov [ rsp + 0x348 ], rbx; spilling x717 to mem
mov [ rsp + 0x350 ], r14; spilling x212 to mem
mulx r14, rbx, [ rsi + 0x38 ]; hix496, lox495<- arg1[5] * arg1[7]
mov rdx, [ rsp + 0x28 ]; load m64 x706 to register64
adox rdx, [ rsp + 0x78 ]
mov [ rsp + 0x358 ], r14; spilling x496 to mem
mov r14, rdx; preserving value of x719 into a new reg
mov rdx, [ rsi + 0x18 ]; saving arg1[3] in rdx.
mov [ rsp + 0x360 ], r9; spilling x77 to mem
mov [ rsp + 0x368 ], rbx; spilling x495 to mem
mulx rbx, r9, [ rsi + 0x20 ]; hix300, lox299<- arg1[3] * arg1[4]
setc dl;
mov [ rsp + 0x370 ], r14; spilling x719 to mem
movzx r14, byte [ rsp + 0x2d8 ]; load byte memx114 to register64
clc;
mov [ rsp + 0x378 ], rcx; spilling x62 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r14, rcx; loading flag
adcx r11, [ rsp + 0x120 ]
adcx r13, [ rsp + 0x18 ]
mov r14b, dl; preserving value of x417 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov [ rsp + 0x380 ], r13; spilling x117 to mem
mulx r13, rcx, [ rsi + 0x10 ]; hix193, lox192<- arg1[2] * arg1[7]
mov rdx, [ rsp + 0x8 ]; load m64 x504 to register64
mov [ rsp + 0x388 ], r11; spilling x115 to mem
seto r11b;
mov byte [ rsp + 0x390 ], r14b; spilling byte x417 to mem
movzx r14, byte [ rsp + 0x2d0 ]; load byte memx516 to register64
mov [ rsp + 0x398 ], r13; spilling x193 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r14, r13; loading flag
adox rdx, [ rsp + 0x38 ]
adox r10, [ rsp + 0x30 ]
adox r8, [ rsp - 0x18 ]
mov r14, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, r14; 0x32ea0103e01090bb, swapping with x517, which is currently in rdx
mov [ rsp + 0x3a0 ], r8; spilling x521 to mem
mulx r8, r13, r12; hix49, lox48<- x40 * 0x32ea0103e01090bb
mov rdx, [ rsp + 0x0 ]; load m64 x94 to register64
adcx rdx, [ rsp - 0x20 ]
mov [ rsp + 0x3a8 ], r10; spilling x519 to mem
mov r10, rdx; preserving value of x119 into a new reg
mov rdx, [ rsi + 0x28 ]; saving arg1[5] in rdx.
mov byte [ rsp + 0x3b0 ], r11b; spilling byte x720 to mem
mov [ rsp + 0x3b8 ], r14; spilling x517 to mem
mulx r14, r11, [ rsi + 0x18 ]; hix298, lox297<- arg1[3] * arg1[5]
seto dl;
mov [ rsp + 0x3c0 ], r14; spilling x298 to mem
movzx r14, byte [ rsp + 0x1f0 ]; load byte memx314 to register64
mov [ rsp + 0x3c8 ], r10; spilling x119 to mem
mov r10, 0x0 ; moving imm to reg
dec r10; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r10; loading flag
adox r9, [ rsp - 0x28 ]
adox r11, rbx
setc r14b;
clc;
adcx r15, [ rsp + 0x40 ]
mov rbx, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r15; x122, swapping with x522, which is currently in rdx
mov [ rsp + 0x3d0 ], r11; spilling x317 to mem
mulx r11, r10, rbx; hi_, lox140<- x122 * 0x6efa1180a5fe67fd
mov r11, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, r10; x140, swapping with x122, which is currently in rdx
mov [ rsp + 0x3d8 ], r9; spilling x315 to mem
mulx r9, rbx, r11; hix149, lox148<- x140 * 0x32ea0103e01090bb
mov r11, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x3e0 ], r9; spilling x149 to mem
mov [ rsp + 0x3e8 ], rbx; spilling x148 to mem
mulx rbx, r9, r11; hix157, lox156<- x140 * 0xa13d118db8bfd2ab
mov r11, rdx; preserving value of x140 into a new reg
mov rdx, [ rsi + 0x20 ]; saving arg1[4] in rdx.
mov [ rsp + 0x3f0 ], rbx; spilling x157 to mem
mov [ rsp + 0x3f8 ], r9; spilling x156 to mem
mulx r9, rbx, [ rsi + 0x38 ]; hix395, lox394<- arg1[4] * arg1[7]
mov rdx, 0x155556ffff39ca9b ; moving imm to reg
mov [ rsp + 0x400 ], r9; spilling x395 to mem
mov [ rsp + 0x408 ], rbx; spilling x394 to mem
mulx rbx, r9, r11; hix143, lox142<- x140 * 0x155556ffff39ca9b
seto dl;
mov [ rsp + 0x410 ], rbx; spilling x143 to mem
mov rbx, 0x0 ; moving imm to reg
dec rbx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rdi, dil
adox rdi, rbx; loading flag
adox r13, [ rsp + 0x148 ]
mov rdi, [ rsp + 0x310 ]; load m64 x194 to register64
setc bl;
clc;
mov byte [ rsp + 0x418 ], dl; spilling byte x318 to mem
mov rdx, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdx; loading flag
adcx rdi, [ rsp + 0x2c8 ]
mov rax, 0xcb8ac8495d187e8c ; moving imm to reg
mov rdx, r11; x140 to rdx
mov [ rsp + 0x420 ], rdi; spilling x218 to mem
mulx rdi, r11, rax; hix147, lox146<- x140 * 0xcb8ac8495d187e8c
xchg rdx, rax; 0xcb8ac8495d187e8c, swapping with x140, which is currently in rdx
mov [ rsp + 0x428 ], r9; spilling x142 to mem
mov [ rsp + 0x430 ], rdi; spilling x147 to mem
mulx rdi, r9, r12; hix47, lox46<- x40 * 0xcb8ac8495d187e8c
mov r12, [ rsp + 0x1e8 ]; load m64 x29 to register64
setc dl;
clc;
mov [ rsp + 0x438 ], r11; spilling x146 to mem
mov r11, -0x1 ; moving imm to reg
movzx rbp, bpl
adcx rbp, r11; loading flag
adcx r12, [ rsp + 0x378 ]
adcx r13, [ rsp + 0x290 ]
mov rbp, [ rsp + 0x368 ]; load m64 x495 to register64
setc r11b;
clc;
mov [ rsp + 0x440 ], r13; spilling x81 to mem
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r13; loading flag
adcx rbp, [ rsp - 0x30 ]
mov r15, 0x626e85bf7c18a0f0 ; moving imm to reg
xchg rdx, r15; 0x626e85bf7c18a0f0, swapping with x219, which is currently in rdx
mov [ rsp + 0x448 ], rbp; spilling x523 to mem
mulx rbp, r13, rax; hix151, lox150<- x140 * 0x626e85bf7c18a0f0
adox r9, r8
movzx r8, r14b;
mov rdx, [ rsp - 0x38 ]; load m64 x92 to register64
lea r8, [ r8 + rdx ]; r8/64 + m8
adox rdi, [ rsp + 0x1b0 ]
mov rdx, [ rsi + 0x30 ]; arg1[6] to rdx
mov [ rsp + 0x450 ], r8; spilling x121 to mem
mulx r8, r14, [ rsi + 0x20 ]; hix397, lox396<- arg1[4] * arg1[6]
mov rdx, [ rsp + 0x188 ]; load m64 x42 to register64
adox rdx, [ rsp + 0x1a8 ]
mov [ rsp + 0x458 ], rbp; spilling x151 to mem
setc bpl;
clc;
mov [ rsp + 0x460 ], r13; spilling x150 to mem
mov r13, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r13; loading flag
adcx rcx, [ rsp + 0x308 ]
mov r15, [ rsp + 0x288 ]; load m64 x107 to register64
seto r13b;
mov byte [ rsp + 0x468 ], bpl; spilling byte x524 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, rbp; loading flag
adox r15, [ rsp + 0x360 ]
mov rbx, [ rsp + 0x398 ];
mov rbp, 0x0 ; moving imm to reg
adcx rbx, rbp
mov rbp, [ rsp - 0x40 ]; load m64 x401 to register64
mov [ rsp + 0x470 ], rbx; spilling x222 to mem
movzx rbx, byte [ rsp + 0x390 ]; load byte memx417 to register64
clc;
mov [ rsp + 0x478 ], rcx; spilling x220 to mem
mov rcx, -0x1 ; moving imm to reg
adcx rbx, rcx; loading flag
adcx rbp, [ rsp - 0x8 ]
adcx r14, [ rsp - 0x10 ]
adcx r8, [ rsp + 0x408 ]
mov rbx, 0xee63bd076e8d9300 ; moving imm to reg
xchg rdx, rax; x140, swapping with x70, which is currently in rdx
mov [ rsp + 0x480 ], r8; spilling x422 to mem
mulx r8, rcx, rbx; hix155, lox154<- x140 * 0xee63bd076e8d9300
adox r12, [ rsp + 0x2b0 ]
setc bl;
clc;
adcx r10, [ rsp + 0x3f8 ]
mov r10, [ rsp + 0x2a8 ]; load m64 x111 to register64
adox r10, [ rsp + 0x440 ]
mov [ rsp + 0x488 ], r14; spilling x420 to mem
setc r14b;
clc;
mov byte [ rsp + 0x490 ], bl; spilling byte x423 to mem
mov rbx, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, rbx; loading flag
adcx r9, [ rsp + 0x280 ]
mov r11, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x498 ], rbp; spilling x418 to mem
mulx rbp, rbx, r11; hix153, lox152<- x140 * 0xcfcb5c6071bad3d2
seto r11b;
mov [ rsp + 0x4a0 ], r10; spilling x128 to mem
mov r10, -0x2 ; moving imm to reg
inc r10; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rcx, [ rsp + 0x3f0 ]
adox rbx, r8
setc r8b;
clc;
movzx r14, r14b
adcx r14, r10; loading flag
adcx r15, rcx
setc r14b;
clc;
adcx r15, [ rsp + 0xa0 ]
seto cl;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r10; loading flag
adox r9, [ rsp + 0x298 ]
movzx r11, byte [ rsp + 0x318 ];
mov r10, [ rsp + 0x60 ]; load m64 x10 to register64
lea r11, [ r11 + r10 ]; r8/64 + m8
mov r10, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r15; x223, swapping with x140, which is currently in rdx
mov [ rsp + 0x4a8 ], r9; spilling x130 to mem
mov [ rsp + 0x4b0 ], r11; spilling x39 to mem
mulx r11, r9, r10; hi_, lox241<- x223 * 0x6efa1180a5fe67fd
mov r11, 0xee63bd076e8d9300 ; moving imm to reg
xchg rdx, r9; x241, swapping with x223, which is currently in rdx
mov [ rsp + 0x4b8 ], rbp; spilling x153 to mem
mulx rbp, r10, r11; hix256, lox255<- x241 * 0xee63bd076e8d9300
mov r11, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x4c0 ], rbp; spilling x256 to mem
mov byte [ rsp + 0x4c8 ], cl; spilling byte x161 to mem
mulx rcx, rbp, r11; hix252, lox251<- x241 * 0x626e85bf7c18a0f0
setc r11b;
clc;
mov [ rsp + 0x4d0 ], rcx; spilling x252 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rcx; loading flag
adcx rdi, [ rsp + 0x278 ]
adcx rax, [ rsp + 0x2c0 ]
adox rdi, [ rsp + 0x388 ]
movzx r8, r13b;
mov rcx, [ rsp + 0x180 ]; load m64 x43 to register64
lea r8, [ r8 + rcx ]; r8/64 + m8
mov rcx, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x4d8 ], rdi; spilling x132 to mem
mulx rdi, r13, rcx; hix250, lox249<- x241 * 0x32ea0103e01090bb
mov rcx, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x4e0 ], rdi; spilling x250 to mem
mov [ rsp + 0x4e8 ], r13; spilling x249 to mem
mulx r13, rdi, rcx; hix258, lox257<- x241 * 0xa13d118db8bfd2ab
seto cl;
mov [ rsp + 0x4f0 ], rdi; spilling x257 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, rdi; loading flag
adox r12, rbx
setc bl;
clc;
adcx r10, r13
mov r14, [ rsp + 0x4b8 ]; load m64 x153 to register64
setc r13b;
movzx rdi, byte [ rsp + 0x4c8 ]; load byte memx161 to register64
clc;
mov [ rsp + 0x4f8 ], r10; spilling x259 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdi, r10; loading flag
adcx r14, [ rsp + 0x460 ]
adox r14, [ rsp + 0x4a0 ]
mov rdi, [ rsp + 0x458 ]; load m64 x151 to register64
adcx rdi, [ rsp + 0x3e8 ]
mov r10, [ rsp + 0x3e0 ]; load m64 x149 to register64
adcx r10, [ rsp + 0x438 ]
mov [ rsp + 0x500 ], r10; spilling x166 to mem
setc r10b;
clc;
mov [ rsp + 0x508 ], rdi; spilling x164 to mem
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx rax, [ rsp + 0x380 ]
mov rcx, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x510 ], rax; spilling x134 to mem
mulx rax, rdi, rcx; hix254, lox253<- x241 * 0xcfcb5c6071bad3d2
seto cl;
mov byte [ rsp + 0x518 ], r10b; spilling byte x167 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r10; loading flag
adox r8, [ rsp + 0x4b0 ]
seto bl;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r10, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, r10; loading flag
adox rdi, [ rsp + 0x4c0 ]
adcx r8, [ rsp + 0x3c8 ]
adox rbp, rax
seto r13b;
inc r10; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, rax; loading flag
adox r12, [ rsp + 0x190 ]
mov r11, [ rsp + 0x4e8 ]; load m64 x249 to register64
seto r10b;
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rax, -0x1 ; moving imm to reg
movzx r13, r13b
adox r13, rax; loading flag
adox r11, [ rsp + 0x4d0 ]
mov r13, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
xchg rdx, r15; x140, swapping with x241, which is currently in rdx
mov byte [ rsp + 0x520 ], bl; spilling byte x90 to mem
mulx rbx, rax, r13; hix145, lox144<- x140 * 0xfcedf2b4f9c0ecf6
seto dl;
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r10, r10b
adox r10, r13; loading flag
adox r14, [ rsp + 0x270 ]
seto r10b;
movzx r13, byte [ rsp + 0x518 ]; load byte memx167 to register64
mov [ rsp + 0x528 ], r8; spilling x136 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r13, r8; loading flag
adox rax, [ rsp + 0x430 ]
mov r13, [ rsp + 0x508 ]; load m64 x164 to register64
seto r8b;
mov [ rsp + 0x530 ], rbx; spilling x145 to mem
mov rbx, -0x1 ; moving imm to reg
inc rbx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbx, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbx; loading flag
adox r13, [ rsp + 0x4a8 ]
seto cl;
inc rbx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r9, [ rsp + 0x4f0 ]
setc r9b;
clc;
mov rbx, -0x1 ; moving imm to reg
movzx r10, r10b
adcx r10, rbx; loading flag
adcx r13, [ rsp + 0x350 ]
mov r10, 0xcb8ac8495d187e8c ; moving imm to reg
xchg rdx, r15; x241, swapping with x266, which is currently in rdx
mov byte [ rsp + 0x538 ], r9b; spilling byte x137 to mem
mulx r9, rbx, r10; hix248, lox247<- x241 * 0xcb8ac8495d187e8c
mov r10, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov byte [ rsp + 0x540 ], r8b; spilling byte x169 to mem
mov [ rsp + 0x548 ], r11; spilling x265 to mem
mulx r11, r8, r10; hix246, lox245<- x241 * 0xfcedf2b4f9c0ecf6
mov r10, [ rsp + 0x4d8 ]; load m64 x132 to register64
mov [ rsp + 0x550 ], rbp; spilling x263 to mem
seto bpl;
mov [ rsp + 0x558 ], r13; spilling x229 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r13; loading flag
adox r10, [ rsp + 0x500 ]
mov rcx, 0x155556ffff39ca9b ; moving imm to reg
mov [ rsp + 0x560 ], r11; spilling x246 to mem
mulx r11, r13, rcx; hix244, lox243<- x241 * 0x155556ffff39ca9b
adcx r10, [ rsp + 0x340 ]
adox rax, [ rsp + 0x510 ]
setc dl;
clc;
mov rcx, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, rcx; loading flag
adcx rbx, [ rsp + 0x4e0 ]
adcx r8, r9
setc r15b;
clc;
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx r12, [ rsp + 0x4f8 ]
seto bpl;
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r12, [ rsp + 0x168 ]
adcx rdi, r14
mov r14, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r14; 0x6efa1180a5fe67fd, swapping with x232, which is currently in rdx
mulx rcx, r9, r12; hi_, lox342<- x324 * 0x6efa1180a5fe67fd
mov rcx, 0x626e85bf7c18a0f0 ; moving imm to reg
mov rdx, rcx; 0x626e85bf7c18a0f0 to rdx
mov [ rsp + 0x568 ], r11; spilling x244 to mem
mulx r11, rcx, r9; hix353, lox352<- x342 * 0x626e85bf7c18a0f0
mov rdx, [ rsi + 0x18 ]; arg1[3] to rdx
mov [ rsp + 0x570 ], r11; spilling x353 to mem
mov [ rsp + 0x578 ], r8; spilling x269 to mem
mulx r8, r11, [ rsi + 0x30 ]; hix296, lox295<- arg1[3] * arg1[6]
mov rdx, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x580 ], r8; spilling x296 to mem
mov [ rsp + 0x588 ], rcx; spilling x352 to mem
mulx rcx, r8, r9; hix357, lox356<- x342 * 0xee63bd076e8d9300
setc dl;
clc;
mov [ rsp + 0x590 ], r11; spilling x295 to mem
mov r11, -0x1 ; moving imm to reg
movzx r15, r15b
adcx r15, r11; loading flag
adcx r13, [ rsp + 0x560 ]
mov r15, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r15; 0x155556ffff39ca9b, swapping with x279, which is currently in rdx
mov [ rsp + 0x598 ], r13; spilling x271 to mem
mulx r13, r11, r9; hix345, lox344<- x342 * 0x155556ffff39ca9b
mov rdx, [ rsp + 0x558 ]; load m64 x229 to register64
mov [ rsp + 0x5a0 ], r13; spilling x345 to mem
seto r13b;
mov [ rsp + 0x5a8 ], r11; spilling x344 to mem
mov r11, 0x0 ; moving imm to reg
dec r11; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, r11; loading flag
adox rdx, [ rsp + 0x550 ]
setc r15b;
clc;
movzx r13, r13b
adcx r13, r11; loading flag
adcx rdi, [ rsp + 0x1a0 ]
mov r13, 0xcb8ac8495d187e8c ; moving imm to reg
xchg rdx, r9; x342, swapping with x280, which is currently in rdx
mov byte [ rsp + 0x5b0 ], r15b; spilling byte x272 to mem
mulx r15, r11, r13; hix349, lox348<- x342 * 0xcb8ac8495d187e8c
adcx r9, [ rsp + 0x1c0 ]
adox r10, [ rsp + 0x548 ]
setc r13b;
clc;
mov [ rsp + 0x5b8 ], r15; spilling x349 to mem
mov r15, -0x1 ; moving imm to reg
movzx r14, r14b
adcx r14, r15; loading flag
adcx rax, [ rsp + 0x338 ]
mov r14, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x5c0 ], r11; spilling x348 to mem
mulx r11, r15, r14; hix347, lox346<- x342 * 0xfcedf2b4f9c0ecf6
adox rbx, rax
mov rax, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x5c8 ], r11; spilling x347 to mem
mulx r11, r14, rax; hix359, lox358<- x342 * 0xa13d118db8bfd2ab
mov rax, [ rsp + 0x428 ]; load m64 x142 to register64
mov [ rsp + 0x5d0 ], rbx; spilling x284 to mem
seto bl;
mov [ rsp + 0x5d8 ], r15; spilling x346 to mem
movzx r15, byte [ rsp + 0x540 ]; load byte memx169 to register64
mov [ rsp + 0x5e0 ], r9; spilling x328 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r15, r9; loading flag
adox rax, [ rsp + 0x530 ]
mov r15, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x5e8 ], r10; spilling x282 to mem
mulx r10, r9, r15; hix351, lox350<- x342 * 0x32ea0103e01090bb
seto r15b;
mov [ rsp + 0x5f0 ], r10; spilling x351 to mem
mov r10, -0x1 ; moving imm to reg
inc r10; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r10; loading flag
adox rax, [ rsp + 0x528 ]
setc bpl;
clc;
adcx r14, r12
setc r14b;
clc;
adcx r8, r11
mov r12, 0xcfcb5c6071bad3d2 ; moving imm to reg
mulx r10, r11, r12; hix355, lox354<- x342 * 0xcfcb5c6071bad3d2
seto dl;
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r14, r14b
adox r14, r12; loading flag
adox rdi, r8
seto r14b;
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp + 0x10 ]
adcx r11, rcx
mov rcx, [ rsp + 0x590 ]; load m64 x295 to register64
setc r8b;
movzx r12, byte [ rsp + 0x418 ]; load byte memx318 to register64
clc;
mov [ rsp + 0x5f8 ], r9; spilling x350 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx rcx, [ rsp + 0x3c0 ]
seto r12b;
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r9; loading flag
adox r10, [ rsp + 0x588 ]
mov r8, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, rdi; x425, swapping with x188, which is currently in rdx
mov [ rsp + 0x600 ], rcx; spilling x319 to mem
mulx rcx, r9, r8; hi_, lox443<- x425 * 0x6efa1180a5fe67fd
movzx rcx, byte [ rsp + 0x520 ]; load byte memx90 to register64
seto r8b;
mov [ rsp + 0x608 ], r10; spilling x364 to mem
movzx r10, byte [ rsp + 0x538 ]; load byte memx137 to register64
mov byte [ rsp + 0x610 ], r12b; spilling byte x426 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox r10, r12; loading flag
adox rcx, [ rsp + 0x450 ]
mov r10, 0xee63bd076e8d9300 ; moving imm to reg
xchg rdx, r9; x443, swapping with x425, which is currently in rdx
mov byte [ rsp + 0x618 ], r8b; spilling byte x365 to mem
mulx r8, r12, r10; hix458, lox457<- x443 * 0xee63bd076e8d9300
mov r10, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x620 ], r8; spilling x458 to mem
mov [ rsp + 0x628 ], r12; spilling x457 to mem
mulx r12, r8, r10; hix448, lox447<- x443 * 0xfcedf2b4f9c0ecf6
movzx r10, r15b;
mov [ rsp + 0x630 ], r12; spilling x448 to mem
mov r12, [ rsp + 0x410 ]; load m64 x143 to register64
lea r10, [ r10 + r12 ]; r8/64 + m8
seto r12b;
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r15; loading flag
adox rax, [ rsp + 0x420 ]
seto bpl;
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx rbx, bl
adox rbx, r15; loading flag
adox rax, [ rsp + 0x578 ]
setc bl;
clc;
movzx rdi, dil
adcx rdi, r15; loading flag
adcx rcx, r10
movzx rdi, r12b;
mov r10, 0x0 ; moving imm to reg
adcx rdi, r10
clc;
movzx rbp, bpl
adcx rbp, r15; loading flag
adcx rcx, [ rsp + 0x478 ]
mov r12, [ rsp + 0x1b8 ]; load m64 x313 to register64
setc bpl;
clc;
movzx r13, r13b
adcx r13, r15; loading flag
adcx r12, [ rsp + 0x5e8 ]
adox rcx, [ rsp + 0x598 ]
seto r13b;
inc r15; OF<-0x0, preserve CF (debug: state 1(-0x1) (thanks Paul))
mov r10, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, r10; loading flag
adox r11, [ rsp + 0x5e0 ]
mov r14, [ rsp + 0x5f8 ]; load m64 x350 to register64
seto r15b;
movzx r10, byte [ rsp + 0x618 ]; load byte memx365 to register64
mov [ rsp + 0x638 ], r8; spilling x447 to mem
mov r8, -0x1 ; moving imm to reg
inc r8; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r8, -0x1 ; moving imm to reg
adox r10, r8; loading flag
adox r14, [ rsp + 0x570 ]
setc r10b;
movzx r8, byte [ rsp + 0x610 ]; load byte memx426 to register64
clc;
mov byte [ rsp + 0x640 ], bl; spilling byte x320 to mem
mov rbx, -0x1 ; moving imm to reg
adcx r8, rbx; loading flag
adcx r11, [ rsp + 0x268 ]
setc r8b;
clc;
movzx r15, r15b
adcx r15, rbx; loading flag
adcx r12, [ rsp + 0x608 ]
mov r15, [ rsp + 0x5c0 ]; load m64 x348 to register64
adox r15, [ rsp + 0x5f0 ]
mov rbx, 0xa13d118db8bfd2ab ; moving imm to reg
mov byte [ rsp + 0x648 ], r13b; spilling byte x289 to mem
mov [ rsp + 0x650 ], r15; spilling x368 to mem
mulx r15, r13, rbx; hix460, lox459<- x443 * 0xa13d118db8bfd2ab
mov rbx, [ rsp + 0x5b8 ]; load m64 x349 to register64
adox rbx, [ rsp + 0x5d8 ]
mov [ rsp + 0x658 ], rbx; spilling x370 to mem
mov rbx, [ rsp + 0x5d0 ]; load m64 x284 to register64
mov [ rsp + 0x660 ], rdi; spilling x191 to mem
seto dil;
mov byte [ rsp + 0x668 ], bpl; spilling byte x238 to mem
mov rbp, -0x1 ; moving imm to reg
inc rbp; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rbp, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, rbp; loading flag
adox rbx, [ rsp + 0x3d8 ]
adox rax, [ rsp + 0x3d0 ]
setc r10b;
clc;
adcx r13, r9
seto r13b;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox r15, [ rsp + 0x628 ]
seto r9b;
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r13, r13b
adox r13, rbp; loading flag
adox rcx, [ rsp + 0x600 ]
adcx r15, r11
setc r11b;
clc;
movzx r8, r8b
adcx r8, rbp; loading flag
adcx r12, [ rsp + 0x258 ]
setc r8b;
clc;
adcx r15, [ rsp + 0xf8 ]
mov r13, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov byte [ rsp + 0x670 ], dil; spilling byte x371 to mem
mulx rdi, rbp, r13; hix456, lox455<- x443 * 0xcfcb5c6071bad3d2
seto r13b;
mov [ rsp + 0x678 ], rcx; spilling x336 to mem
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, rcx; loading flag
adox rbp, [ rsp + 0x620 ]
mov r9, 0x626e85bf7c18a0f0 ; moving imm to reg
mov byte [ rsp + 0x680 ], r13b; spilling byte x337 to mem
mulx r13, rcx, r9; hix454, lox453<- x443 * 0x626e85bf7c18a0f0
setc r9b;
clc;
mov [ rsp + 0x688 ], r13; spilling x454 to mem
mov r13, -0x1 ; moving imm to reg
movzx r11, r11b
adcx r11, r13; loading flag
adcx r12, rbp
setc r11b;
clc;
movzx r10, r10b
adcx r10, r13; loading flag
adcx rbx, r14
movzx r14, byte [ rsp + 0x5b0 ];
mov r10, [ rsp + 0x568 ]; load m64 x244 to register64
lea r14, [ r14 + r10 ]; r8/64 + m8
mov r10, [ rsp + 0x660 ]; load m64 x191 to register64
seto bpl;
movzx r13, byte [ rsp + 0x668 ]; load byte memx238 to register64
mov byte [ rsp + 0x690 ], r11b; spilling byte x481 to mem
mov r11, -0x1 ; moving imm to reg
inc r11; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r11, -0x1 ; moving imm to reg
adox r13, r11; loading flag
adox r10, [ rsp + 0x470 ]
mov r13, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, r15; x526, swapping with x443, which is currently in rdx
mov [ rsp + 0x698 ], rbx; spilling x383 to mem
mulx rbx, r11, r13; hi_, lox544<- x526 * 0x6efa1180a5fe67fd
mov rbx, rdx; preserving value of x526 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mov byte [ rsp + 0x6a0 ], r8b; spilling byte x430 to mem
mulx r8, r13, [ rsi + 0x18 ]; hix294, lox293<- arg1[3] * arg1[7]
mov rdx, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x6a8 ], r8; spilling x294 to mem
mov [ rsp + 0x6b0 ], r13; spilling x293 to mem
mulx r13, r8, r11; hix553, lox552<- x544 * 0x32ea0103e01090bb
adcx rax, [ rsp + 0x650 ]
mov rdx, 0xee63bd076e8d9300 ; moving imm to reg
mov [ rsp + 0x6b8 ], r13; spilling x553 to mem
mov [ rsp + 0x6c0 ], r8; spilling x552 to mem
mulx r8, r13, r11; hix559, lox558<- x544 * 0xee63bd076e8d9300
seto dl;
mov [ rsp + 0x6c8 ], r8; spilling x559 to mem
movzx r8, byte [ rsp + 0x648 ]; load byte memx289 to register64
mov [ rsp + 0x6d0 ], r13; spilling x558 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox r8, r13; loading flag
adox r10, r14
mov r8, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r11; x544, swapping with x240, which is currently in rdx
mulx r13, r14, r8; hix547, lox546<- x544 * 0x155556ffff39ca9b
mov r8, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x6d8 ], r13; spilling x547 to mem
mov [ rsp + 0x6e0 ], r14; spilling x546 to mem
mulx r14, r13, r8; hix551, lox550<- x544 * 0xcb8ac8495d187e8c
mov r8, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x6e8 ], r14; spilling x551 to mem
mov [ rsp + 0x6f0 ], r13; spilling x550 to mem
mulx r13, r14, r8; hix557, lox556<- x544 * 0xcfcb5c6071bad3d2
mov r8, 0xa13d118db8bfd2ab ; moving imm to reg
mov byte [ rsp + 0x6f8 ], r11b; spilling byte x240 to mem
mov [ rsp + 0x700 ], r13; spilling x557 to mem
mulx r13, r11, r8; hix561, lox560<- x544 * 0xa13d118db8bfd2ab
setc r8b;
clc;
mov [ rsp + 0x708 ], r11; spilling x560 to mem
mov r11, -0x1 ; moving imm to reg
movzx r9, r9b
adcx r9, r11; loading flag
adcx r12, [ rsp + 0x118 ]
mov r9, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x710 ], r12; spilling x528 to mem
mulx r12, r11, r9; hix555, lox554<- x544 * 0x626e85bf7c18a0f0
seto r9b;
mov [ rsp + 0x718 ], r12; spilling x555 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r12; loading flag
adox rdi, rcx
mov rbp, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mulx r12, rcx, rbp; hix549, lox548<- x544 * 0xfcedf2b4f9c0ecf6
mov rdx, [ rsp + 0x330 ]; load m64 x414 to register64
setc bpl;
mov [ rsp + 0x720 ], r12; spilling x549 to mem
movzx r12, byte [ rsp + 0x6a0 ]; load byte memx430 to register64
clc;
mov [ rsp + 0x728 ], rcx; spilling x548 to mem
mov rcx, -0x1 ; moving imm to reg
adcx r12, rcx; loading flag
adcx rdx, [ rsp + 0x698 ]
setc r12b;
movzx rcx, byte [ rsp + 0x690 ]; load byte memx481 to register64
clc;
mov byte [ rsp + 0x730 ], r9b; spilling byte x291 to mem
mov r9, -0x1 ; moving imm to reg
adcx rcx, r9; loading flag
adcx rdx, rdi
mov rcx, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, rcx; 0x32ea0103e01090bb, swapping with x482, which is currently in rdx
mulx r9, rdi, r15; hix452, lox451<- x443 * 0x32ea0103e01090bb
adox rdi, [ rsp + 0x688 ]
seto dl;
mov [ rsp + 0x738 ], rdi; spilling x467 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, rdi; loading flag
adox rax, [ rsp + 0x328 ]
mov r12, [ rsp + 0x580 ]; load m64 x296 to register64
seto dil;
mov [ rsp + 0x740 ], rax; spilling x433 to mem
movzx rax, byte [ rsp + 0x640 ]; load byte memx320 to register64
mov [ rsp + 0x748 ], rcx; spilling x482 to mem
mov rcx, -0x1 ; moving imm to reg
inc rcx; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rcx, -0x1 ; moving imm to reg
adox rax, rcx; loading flag
adox r12, [ rsp + 0x6b0 ]
setc al;
clc;
adcx r13, [ rsp + 0x6d0 ]
adcx r14, [ rsp + 0x6c8 ]
seto cl;
mov [ rsp + 0x750 ], r14; spilling x564 to mem
movzx r14, byte [ rsp + 0x680 ]; load byte memx337 to register64
mov [ rsp + 0x758 ], r13; spilling x562 to mem
mov r13, 0x0 ; moving imm to reg
dec r13; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r13; loading flag
adox r10, r12
mov r14, 0xcb8ac8495d187e8c ; moving imm to reg
xchg rdx, r15; x443, swapping with x468, which is currently in rdx
mulx r13, r12, r14; hix450, lox449<- x443 * 0xcb8ac8495d187e8c
mov r14, [ rsp + 0x678 ]; load m64 x336 to register64
mov byte [ rsp + 0x760 ], al; spilling byte x483 to mem
setc al;
clc;
mov byte [ rsp + 0x768 ], cl; spilling byte x322 to mem
mov rcx, -0x1 ; moving imm to reg
movzx r8, r8b
adcx r8, rcx; loading flag
adcx r14, [ rsp + 0x658 ]
seto r8b;
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx r15, r15b
adox r15, rcx; loading flag
adox r9, r12
setc r15b;
clc;
movzx rax, al
adcx rax, rcx; loading flag
adcx r11, [ rsp + 0x700 ]
adox r13, [ rsp + 0x638 ]
mov rax, [ rsp + 0x748 ]; load m64 x482 to register64
setc r12b;
clc;
movzx rbp, bpl
adcx rbp, rcx; loading flag
adcx rax, [ rsp + 0x250 ]
seto bpl;
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rcx, -0x1 ; moving imm to reg
movzx rdi, dil
adox rdi, rcx; loading flag
adox r14, [ rsp + 0x498 ]
mov rdi, [ rsp + 0x5c8 ]; load m64 x347 to register64
setc cl;
mov byte [ rsp + 0x770 ], bpl; spilling byte x472 to mem
movzx rbp, byte [ rsp + 0x670 ]; load byte memx371 to register64
clc;
mov [ rsp + 0x778 ], r13; spilling x471 to mem
mov r13, -0x1 ; moving imm to reg
adcx rbp, r13; loading flag
adcx rdi, [ rsp + 0x5a8 ]
setc bpl;
clc;
movzx r15, r15b
adcx r15, r13; loading flag
adcx r10, rdi
movzx r15, byte [ rsp + 0x768 ];
mov rdi, [ rsp + 0x6a8 ]; load m64 x294 to register64
lea r15, [ r15 + rdi ]; r8/64 + m8
movzx rdi, bpl;
mov r13, [ rsp + 0x5a0 ]; load m64 x345 to register64
lea rdi, [ rdi + r13 ]; r8/64 + m8
mov r13, [ rsp + 0x740 ]; load m64 x433 to register64
seto bpl;
mov [ rsp + 0x780 ], r10; spilling x389 to mem
movzx r10, byte [ rsp + 0x760 ]; load byte memx483 to register64
mov [ rsp + 0x788 ], rdi; spilling x374 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, rdi; loading flag
adox r13, [ rsp + 0x738 ]
setc r10b;
clc;
movzx rcx, cl
adcx rcx, rdi; loading flag
adcx r13, [ rsp + 0x248 ]
adox r9, r14
seto cl;
inc rdi; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rbx, [ rsp + 0x708 ]
mov rbx, rdx; preserving value of x443 into a new reg
mov rdx, [ rsi + 0x38 ]; saving arg1[7] in rdx.
mulx rdi, r14, [ rsi + 0x28 ]; hix702, lox701<- arg1[7] * arg1[5]
mov rdx, [ rsp + 0x758 ]; load m64 x562 to register64
adox rdx, [ rsp + 0x710 ]
adox rax, [ rsp + 0x750 ]
mov [ rsp + 0x790 ], rdi; spilling x702 to mem
movzx rdi, byte [ rsp + 0x490 ];
mov [ rsp + 0x798 ], r14; spilling x701 to mem
mov r14, [ rsp + 0x400 ]; load m64 x395 to register64
lea rdi, [ rdi + r14 ]; r8/64 + m8
seto r14b;
mov [ rsp + 0x7a0 ], rdi; spilling x424 to mem
mov rdi, -0x2 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox rdx, [ rsp + 0x20 ]
adox rax, [ rsp + 0x1e0 ]
mov rdi, 0x6efa1180a5fe67fd ; moving imm to reg
mov [ rsp + 0x7a8 ], r9; spilling x486 to mem
mov [ rsp + 0x7b0 ], rax; spilling x629 to mem
mulx rax, r9, rdi; hi_, lox645<- x627 * 0x6efa1180a5fe67fd
seto al;
mov rdi, -0x1 ; moving imm to reg
inc rdi; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rdi, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdi; loading flag
adox r13, r11
mov r11, 0x155556ffff39ca9b ; moving imm to reg
xchg rdx, r11; 0x155556ffff39ca9b, swapping with x627, which is currently in rdx
mulx rdi, r14, rbx; hix446, lox445<- x443 * 0x155556ffff39ca9b
movzx rbx, byte [ rsp + 0x730 ];
movzx rdx, byte [ rsp + 0x6f8 ]; load byte memx240 to register64
lea rbx, [ rbx + rdx ]; r64+m8
seto dl;
mov [ rsp + 0x7b8 ], rdi; spilling x446 to mem
mov rdi, 0x0 ; moving imm to reg
dec rdi; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rdi; loading flag
adox r13, [ rsp + 0x240 ]
mov rax, [ rsp + 0x6c0 ]; load m64 x552 to register64
seto dil;
mov [ rsp + 0x7c0 ], r14; spilling x445 to mem
mov r14, 0x0 ; moving imm to reg
dec r14; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r12, r12b
adox r12, r14; loading flag
adox rax, [ rsp + 0x718 ]
seto r12b;
inc r14; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r14, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r14; loading flag
adox rbx, r15
mov r8, [ rsp + 0x6b8 ]; load m64 x553 to register64
setc r15b;
clc;
movzx r12, r12b
adcx r12, r14; loading flag
adcx r8, [ rsp + 0x6f0 ]
setc r12b;
clc;
movzx r10, r10b
adcx r10, r14; loading flag
adcx rbx, [ rsp + 0x788 ]
mov r10, [ rsp + 0x488 ]; load m64 x420 to register64
seto r14b;
mov byte [ rsp + 0x7c8 ], r12b; spilling byte x571 to mem
mov r12, 0x0 ; moving imm to reg
dec r12; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rbp, bpl
adox rbp, r12; loading flag
adox r10, [ rsp + 0x780 ]
seto bpl;
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r12; loading flag
adox r10, [ rsp + 0x778 ]
seto cl;
inc r12; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r12, -0x1 ; moving imm to reg
movzx rbp, bpl
adox rbp, r12; loading flag
adox rbx, [ rsp + 0x480 ]
mov rbp, 0x32ea0103e01090bb ; moving imm to reg
xchg rdx, r9; x645, swapping with x584, which is currently in rdx
mov [ rsp + 0x7d0 ], r8; spilling x570 to mem
mulx r8, r12, rbp; hix654, lox653<- x645 * 0x32ea0103e01090bb
mov rbp, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x7d8 ], r10; spilling x488 to mem
mov [ rsp + 0x7e0 ], rbx; spilling x439 to mem
mulx rbx, r10, rbp; hix658, lox657<- x645 * 0xcfcb5c6071bad3d2
mov rbp, 0x155556ffff39ca9b ; moving imm to reg
mov byte [ rsp + 0x7e8 ], cl; spilling byte x489 to mem
mov byte [ rsp + 0x7f0 ], r14b; spilling byte x341 to mem
mulx r14, rcx, rbp; hix648, lox647<- x645 * 0x155556ffff39ca9b
mov rbp, 0xa13d118db8bfd2ab ; moving imm to reg
mov [ rsp + 0x7f8 ], r14; spilling x648 to mem
mov [ rsp + 0x800 ], rcx; spilling x647 to mem
mulx rcx, r14, rbp; hix662, lox661<- x645 * 0xa13d118db8bfd2ab
mov rbp, 0xee63bd076e8d9300 ; moving imm to reg
mov byte [ rsp + 0x808 ], dil; spilling byte x632 to mem
mov [ rsp + 0x810 ], r13; spilling x631 to mem
mulx r13, rdi, rbp; hix660, lox659<- x645 * 0xee63bd076e8d9300
setc bpl;
clc;
adcx rdi, rcx
adcx r10, r13
seto cl;
mov r13, -0x2 ; moving imm to reg
inc r13; OF<-0x0, preserve CF   (debug: 6; load -2, increase it, save as -1)
adox r14, r11
adox rdi, [ rsp + 0x7b0 ]
mov r14, 0x626e85bf7c18a0f0 ; moving imm to reg
mulx r13, r11, r14; hix656, lox655<- x645 * 0x626e85bf7c18a0f0
mov r14, [ rsp + 0x7a8 ]; load m64 x486 to register64
mov byte [ rsp + 0x818 ], cl; spilling byte x440 to mem
seto cl;
mov byte [ rsp + 0x820 ], bpl; spilling byte x392 to mem
mov rbp, 0x0 ; moving imm to reg
dec rbp; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r15, r15b
adox r15, rbp; loading flag
adox r14, [ rsp + 0x3b8 ]
adcx r11, rbx
adcx r12, r13
seto r15b;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
adox rdi, [ rsp - 0x48 ]
seto bl;
dec rbp; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r9, r9b
adox r9, rbp; loading flag
adox r14, rax
mov r9, 0xcb8ac8495d187e8c ; moving imm to reg
mulx r13, rax, r9; hix652, lox651<- x645 * 0xcb8ac8495d187e8c
adcx rax, r8
seto r8b;
inc rbp; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rbp, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rbp; loading flag
adox r10, [ rsp + 0x810 ]
setc cl;
clc;
movzx rbx, bl
adcx rbx, rbp; loading flag
adcx r10, [ rsp + 0xd0 ]
mov rbx, 0x6efa1180a5fe67fd ; moving imm to reg
xchg rdx, rbx; 0x6efa1180a5fe67fd, swapping with x645, which is currently in rdx
mulx r9, rbp, rdi; hi_, lox746<- x728 * 0x6efa1180a5fe67fd
setc r9b;
movzx rdx, byte [ rsp + 0x808 ]; load byte memx632 to register64
clc;
mov [ rsp + 0x828 ], r10; spilling x730 to mem
mov r10, -0x1 ; moving imm to reg
adcx rdx, r10; loading flag
adcx r14, [ rsp + 0x238 ]
mov rdx, [ rsp + 0x7c0 ]; load m64 x445 to register64
seto r10b;
mov [ rsp + 0x830 ], rax; spilling x671 to mem
movzx rax, byte [ rsp + 0x770 ]; load byte memx472 to register64
mov [ rsp + 0x838 ], r12; spilling x669 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
adox rax, r12; loading flag
adox rdx, [ rsp + 0x630 ]
mov rax, 0xee63bd076e8d9300 ; moving imm to reg
xchg rdx, rbp; x746, swapping with x473, which is currently in rdx
mov byte [ rsp + 0x840 ], r9b; spilling byte x731 to mem
mulx r9, r12, rax; hix761, lox760<- x746 * 0xee63bd076e8d9300
mov rax, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x848 ], r9; spilling x761 to mem
mov [ rsp + 0x850 ], r11; spilling x667 to mem
mulx r11, r9, rax; hix759, lox758<- x746 * 0xcfcb5c6071bad3d2
mov rax, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
xchg rdx, rbx; x645, swapping with x746, which is currently in rdx
mov [ rsp + 0x858 ], r11; spilling x759 to mem
mov [ rsp + 0x860 ], r9; spilling x758 to mem
mulx r9, r11, rax; hix650, lox649<- x645 * 0xfcedf2b4f9c0ecf6
mov rdx, [ rsp + 0x7b8 ];
mov rax, 0x0 ; moving imm to reg
adox rdx, rax
mov rax, 0xa13d118db8bfd2ab ; moving imm to reg
xchg rdx, rbx; x746, swapping with x475, which is currently in rdx
mov [ rsp + 0x868 ], r9; spilling x650 to mem
mov [ rsp + 0x870 ], r14; spilling x633 to mem
mulx r14, r9, rax; hix763, lox762<- x746 * 0xa13d118db8bfd2ab
mov rax, [ rsp + 0x70 ]; load m64 x704 to register64
mov byte [ rsp + 0x878 ], r10b; spilling byte x683 to mem
movzx r10, byte [ rsp + 0x3b0 ]; load byte memx720 to register64
mov byte [ rsp + 0x880 ], r8b; spilling byte x586 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r10, r8; loading flag
adox rax, [ rsp + 0x798 ]
movzx r10, byte [ rsp + 0x820 ];
movzx r8, byte [ rsp + 0x7f0 ]; load byte memx341 to register64
lea r10, [ r10 + r8 ]; r64+m8
movzx r8, byte [ rsp + 0x468 ];
mov [ rsp + 0x888 ], rax; spilling x721 to mem
mov rax, [ rsp + 0x358 ]; load m64 x496 to register64
lea r8, [ r8 + rax ]; r8/64 + m8
mov rax, 0xcb8ac8495d187e8c ; moving imm to reg
mov [ rsp + 0x890 ], r8; spilling x525 to mem
mov byte [ rsp + 0x898 ], r15b; spilling byte x535 to mem
mulx r15, r8, rax; hix753, lox752<- x746 * 0xcb8ac8495d187e8c
seto al;
mov [ rsp + 0x8a0 ], r15; spilling x753 to mem
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rcx, cl
adox rcx, r15; loading flag
adox r13, r11
setc cl;
clc;
adcx r12, r14
setc r11b;
clc;
adcx r9, rdi
setc r9b;
movzx rdi, byte [ rsp + 0x818 ]; load byte memx440 to register64
clc;
adcx rdi, r15; loading flag
adcx r10, [ rsp + 0x7a0 ]
setc dil;
movzx r14, byte [ rsp + 0x7e8 ]; load byte memx489 to register64
clc;
adcx r14, r15; loading flag
adcx rbp, [ rsp + 0x7e0 ]
adcx rbx, r10
mov r14, [ rsp + 0x2a0 ]; load m64 x599 to register64
setc r10b;
movzx r15, byte [ rsp + 0x320 ]; load byte memx623 to register64
clc;
mov [ rsp + 0x8a8 ], r13; spilling x673 to mem
mov r13, -0x1 ; moving imm to reg
adcx r15, r13; loading flag
adcx r14, [ rsp + 0x88 ]
mov r15, [ rsp + 0x7d8 ]; load m64 x488 to register64
setc r13b;
mov [ rsp + 0x8b0 ], r12; spilling x764 to mem
movzx r12, byte [ rsp + 0x898 ]; load byte memx535 to register64
clc;
mov byte [ rsp + 0x8b8 ], r9b; spilling byte x780 to mem
mov r9, -0x1 ; moving imm to reg
adcx r12, r9; loading flag
adcx r15, [ rsp + 0x3a8 ]
adcx rbp, [ rsp + 0x3a0 ]
movzx r12, r10b;
movzx rdi, dil
lea r12, [ r12 + rdi ]
seto dil;
movzx r10, byte [ rsp + 0x880 ]; load byte memx586 to register64
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
adox r10, r9; loading flag
adox r15, [ rsp + 0x7d0 ]
seto r10b;
inc r9; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r9, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, r9; loading flag
adox r15, [ rsp + 0x260 ]
mov rcx, [ rsp + 0x870 ]; load m64 x633 to register64
seto r9b;
mov byte [ rsp + 0x8c0 ], dil; spilling byte x674 to mem
movzx rdi, byte [ rsp + 0x878 ]; load byte memx683 to register64
mov byte [ rsp + 0x8c8 ], r13b; spilling byte x625 to mem
mov r13, -0x1 ; moving imm to reg
inc r13; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r13, -0x1 ; moving imm to reg
adox rdi, r13; loading flag
adox rcx, [ rsp + 0x850 ]
mov rdi, [ rsp + 0x6e8 ]; load m64 x551 to register64
seto r13b;
mov [ rsp + 0x8d0 ], r14; spilling x624 to mem
movzx r14, byte [ rsp + 0x7c8 ]; load byte memx571 to register64
mov byte [ rsp + 0x8d8 ], r9b; spilling byte x636 to mem
mov r9, 0x0 ; moving imm to reg
dec r9; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
adox r14, r9; loading flag
adox rdi, [ rsp + 0x728 ]
setc r14b;
movzx r9, byte [ rsp + 0x840 ]; load byte memx731 to register64
clc;
mov [ rsp + 0x8e0 ], r15; spilling x635 to mem
mov r15, -0x1 ; moving imm to reg
adcx r9, r15; loading flag
adcx rcx, [ rsp + 0x178 ]
mov r9, [ rsp + 0x6e0 ]; load m64 x546 to register64
adox r9, [ rsp + 0x720 ]
mov r15, [ rsp + 0x6d8 ];
mov [ rsp + 0x8e8 ], rcx; spilling x732 to mem
mov rcx, 0x0 ; moving imm to reg
adox r15, rcx
dec rcx; OF<-0x0, preserve CF (debug: state 3 (y: 0, n: -1))
movzx r10, r10b
adox r10, rcx; loading flag
adox rbp, rdi
seto r10b;
inc rcx; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx r14, r14b
adox r14, rdi; loading flag
adox rbx, [ rsp + 0x448 ]
adox r12, [ rsp + 0x890 ]
seto r14b;
dec rcx; OF<-0x0, preserve CF (debug: state 1(0x0) (thanks Paul))
movzx r10, r10b
adox r10, rcx; loading flag
adox rbx, r9
mov rdi, 0x626e85bf7c18a0f0 ; moving imm to reg
mulx r10, r9, rdi; hix757, lox756<- x746 * 0x626e85bf7c18a0f0
adox r15, r12
mov r12, [ rsp + 0x790 ]; load m64 x702 to register64
setc cl;
clc;
mov rdi, -0x1 ; moving imm to reg
movzx rax, al
adcx rax, rdi; loading flag
adcx r12, [ rsp + 0x140 ]
mov rax, [ rsp + 0x848 ]; load m64 x761 to register64
seto dil;
mov [ rsp + 0x8f0 ], r12; spilling x723 to mem
mov r12, -0x1 ; moving imm to reg
inc r12; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r12, -0x1 ; moving imm to reg
movzx r11, r11b
adox r11, r12; loading flag
adox rax, [ rsp + 0x860 ]
adox r9, [ rsp + 0x858 ]
mov r11, [ rsp + 0x138 ]; load m64 x700 to register64
adcx r11, [ rsp + 0xb8 ]
mov r12, 0x155556ffff39ca9b ; moving imm to reg
mov [ rsp + 0x8f8 ], r11; spilling x725 to mem
mov [ rsp + 0x900 ], r9; spilling x768 to mem
mulx r9, r11, r12; hix749, lox748<- x746 * 0x155556ffff39ca9b
mov r12, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x908 ], r9; spilling x749 to mem
mov [ rsp + 0x910 ], rax; spilling x766 to mem
mulx rax, r9, r12; hix755, lox754<- x746 * 0x32ea0103e01090bb
adox r9, r10
adox r8, rax
mov r10, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mulx r12, rax, r10; hix751, lox750<- x746 * 0xfcedf2b4f9c0ecf6
mov rdx, [ rsp + 0x838 ]; load m64 x669 to register64
seto r10b;
mov [ rsp + 0x918 ], r8; spilling x772 to mem
mov r8, 0x0 ; moving imm to reg
dec r8; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r13, r13b
adox r13, r8; loading flag
adox rdx, [ rsp + 0x8e0 ]
seto r13b;
inc r8; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r8, -0x1 ; moving imm to reg
movzx r10, r10b
adox r10, r8; loading flag
adox rax, [ rsp + 0x8a0 ]
seto r10b;
movzx r8, byte [ rsp + 0x8d8 ]; load byte memx636 to register64
mov [ rsp + 0x920 ], rax; spilling x774 to mem
mov rax, -0x1 ; moving imm to reg
inc rax; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov rax, -0x1 ; moving imm to reg
adox r8, rax; loading flag
adox rbp, [ rsp + 0x2b8 ]
setc r8b;
clc;
movzx r10, r10b
adcx r10, rax; loading flag
adcx r12, r11
adox rbx, [ rsp + 0x2e0 ]
adox r15, [ rsp + 0x8d0 ]
movzx r11, byte [ rsp + 0x8c8 ];
mov r10, [ rsp + 0x80 ]; load m64 x597 to register64
lea r11, [ r11 + r10 ]; r8/64 + m8
movzx r10, dil;
movzx r14, r14b
lea r10, [ r10 + r14 ]
seto r14b;
inc rax; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov rdi, -0x1 ; moving imm to reg
movzx rcx, cl
adox rcx, rdi; loading flag
adox rdx, [ rsp + 0x348 ]
setc cl;
clc;
movzx r13, r13b
adcx r13, rdi; loading flag
adcx rbp, [ rsp + 0x830 ]
mov r13, [ rsp + 0x800 ]; load m64 x647 to register64
setc al;
movzx rdi, byte [ rsp + 0x8c0 ]; load byte memx674 to register64
clc;
mov [ rsp + 0x928 ], r12; spilling x776 to mem
mov r12, -0x1 ; moving imm to reg
adcx rdi, r12; loading flag
adcx r13, [ rsp + 0x868 ]
mov rdi, [ rsp + 0x828 ]; load m64 x730 to register64
seto r12b;
mov byte [ rsp + 0x930 ], r8b; spilling byte x726 to mem
movzx r8, byte [ rsp + 0x8b8 ]; load byte memx780 to register64
mov [ rsp + 0x938 ], r9; spilling x770 to mem
mov r9, -0x1 ; moving imm to reg
inc r9; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r9, -0x1 ; moving imm to reg
adox r8, r9; loading flag
adox rdi, [ rsp + 0x8b0 ]
setc r8b;
clc;
movzx r14, r14b
adcx r14, r9; loading flag
adcx r10, r11
mov r14, [ rsp + 0x8e8 ]; load m64 x732 to register64
adox r14, [ rsp + 0x910 ]
setc r11b;
clc;
movzx r12, r12b
adcx r12, r9; loading flag
adcx rbp, [ rsp + 0x370 ]
adox rdx, [ rsp + 0x900 ]
movzx r12, cl;
mov r9, [ rsp + 0x908 ]; load m64 x749 to register64
lea r12, [ r12 + r9 ]; r8/64 + m8
seto r9b;
mov rcx, 0x0 ; moving imm to reg
dec rcx; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx rax, al
adox rax, rcx; loading flag
adox rbx, [ rsp + 0x8a8 ]
adcx rbx, [ rsp + 0x888 ]
movzx rax, r8b;
mov rcx, [ rsp + 0x7f8 ]; load m64 x648 to register64
lea rax, [ rax + rcx ]; r8/64 + m8
adox r13, r15
adox rax, r10
movzx rcx, r11b;
mov r15, 0x0 ; moving imm to reg
adox rcx, r15
setc r8b;
mov r10, 0xa13d118db8bfd2ab ; moving imm to reg
mov r11, rdi;
sub r11, r10
mov r15, 0xee63bd076e8d9300 ; moving imm to reg
mov r10, r14;
sbb r10, r15
mov r15, 0x0 ; moving imm to reg
dec r15; OF<-0x0, preserve CF (debug: state 4 (thanks Paul))
movzx r9, r9b
adox r9, r15; loading flag
adox rbp, [ rsp + 0x938 ]
adox rbx, [ rsp + 0x918 ]
seto r9b;
inc r15; OF<-0x0, preserve CF (debug: state 2 (y: -1, n: 0))
mov r15, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r15; loading flag
adox r13, [ rsp + 0x8f0 ]
seto r8b;
mov r15, 0xcfcb5c6071bad3d2 ; moving imm to reg
mov [ rsp + 0x940 ], r10; spilling x800 to mem
mov r10, rdx;
sbb r10, r15
mov r15, 0x626e85bf7c18a0f0 ; moving imm to reg
mov [ rsp + 0x948 ], r10; spilling x802 to mem
mov r10, rbp;
sbb r10, r15
mov r15, -0x1 ; moving imm to reg
inc r15; OF<-0x0, preserve CF (debug: state 5 (thanks Paul))
mov r15, -0x1 ; moving imm to reg
movzx r8, r8b
adox r8, r15; loading flag
adox rax, [ rsp + 0x8f8 ]
setc r8b;
clc;
movzx r9, r9b
adcx r9, r15; loading flag
adcx r13, [ rsp + 0x920 ]
movzx r9, byte [ rsp + 0x930 ];
mov r15, [ rsp + 0xb0 ]; load m64 x698 to register64
lea r9, [ r9 + r15 ]; r8/64 + m8
adcx rax, [ rsp + 0x928 ]
adox r9, rcx
adcx r12, r9
seto r15b;
setc cl;
mov r9, -0x1 ; moving imm to reg
add r9b, r8b; load to CF<-x805
mov r9, 0x32ea0103e01090bb ; moving imm to reg
mov [ rsp + 0x950 ], r10; spilling x804 to mem
mov r10, rbx;
sbb r10, r9
mov r8, 0xcb8ac8495d187e8c ; moving imm to reg
mov r9, r13;
sbb r9, r8
mov r8, 0xfcedf2b4f9c0ecf6 ; moving imm to reg
mov [ rsp + 0x958 ], r9; spilling x808 to mem
mov r9, rax;
sbb r9, r8
movzx r8, cl;
movzx r15, r15b
lea r8, [ r8 + r15 ]
mov r15, 0x155556ffff39ca9b ; moving imm to reg
mov rcx, r12;
sbb rcx, r15
mov r15, 0x0 ; moving imm to reg
sbb r8, r15
cmovc r10, rbx; if CF, x820<- x789 (nzVar)
mov r8, [ rsp - 0x50 ]; load m64 out1 to register64
mov [ r8 + 0x20 ], r10; out1[4] = x820
cmovc r11, rdi; if CF, x816<- x781 (nzVar)
mov rdi, [ rsp + 0x958 ];
cmovc rdi, r13; if CF, x821<- x791 (nzVar)
mov rbx, [ rsp + 0x948 ];
cmovc rbx, rdx; if CF, x818<- x785 (nzVar)
mov [ r8 + 0x28 ], rdi; out1[5] = x821
mov [ r8 + 0x10 ], rbx; out1[2] = x818
mov rdx, [ rsp + 0x940 ];
cmovc rdx, r14; if CF, x817<- x783 (nzVar)
mov [ r8 + 0x8 ], rdx; out1[1] = x817
mov r14, [ rsp + 0x950 ];
cmovc r14, rbp; if CF, x819<- x787 (nzVar)
cmovc rcx, r12; if CF, x823<- x795 (nzVar)
mov [ r8 + 0x38 ], rcx; out1[7] = x823
mov [ r8 + 0x18 ], r14; out1[3] = x819
mov [ r8 + 0x0 ], r11; out1[0] = x816
cmovc r9, rax; if CF, x822<- x793 (nzVar)
mov [ r8 + 0x30 ], r9; out1[6] = x822
mov rbx, [ rsp - 0x80 ]; pop
mov rbp, [ rsp - 0x78 ]; pop
mov r12, [ rsp - 0x70 ]; pop
mov r13, [ rsp - 0x68 ]; pop
mov r14, [ rsp - 0x60 ]; pop
mov r15, [ rsp - 0x58 ]; pop
add rsp, 2528
ret
; cpu AMD Ryzen 7 PRO 7840U w/ Radeon 780M Graphics
; ratio 1.5455
; seed 0001775470853120 
; CC / CFLAGS gcc / -march=native -mtune=native -O3 
; cyclegoal; 10000
; using counter; RDTSCP
; framePointer omit
; memoryConstraints none
; time needed: 9144172 ms on 5000 evaluations.
; Time spent for assembling and measuring (initial batch_size=14, initial num_batches=31): 27862 ms
; number of used evaluations: 5000
; Ratio (time for assembling + measure)/(total runtime for 5000 evals): 0.003046968057906172
; number reverted permutation / tried permutation: 1159 / 2425 =47.794%
; number reverted decision / tried decision: 1148 / 2574 =44.600%