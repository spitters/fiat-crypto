#import "G1.c"

void main() {
	printf("output is: \n");
	uint64_t ox[6];
	uint64_t oy[6];
	uint64_t oz[6];
    /* Coordinates of a point in Montgomery form, not sure why it outputs in plain form. */
	const uint64_t x[6] = {0x5CB38790FD530C16lu, 0x7817FC679976FFF5lu, 0x154F95C7143BA1C1lu, 0xF0AE6ACDF3D0E747lu, 0xEDCE6ECC21DBF440lu, 0x120177419E0BFB75lu};
	const uint64_t y[6] = {0xBAAC93D50CE72271lu, 0x8C22631A7918FD8Elu, 0xDD595F13570725CElu, 0x51AC582950405194lu, 0x0E1C8C3FAD0059C0lu, 0x0BBC3EFC5008A26Alu};
	const uint64_t z[6] = {0x760900000002FFFDlu, 0xEBF4000BC40C0002lu, 0x5F48985753C758BAlu, 0x77CE585370525745lu, 0x5C071A97A256EC6Dlu, 0x15F65EC3FA80E493lu};
	const uint64_t n[4] = {0xFFFFFFFF00000001lu, 0x53BDA402FFFE5BFElu, 0x3339D80809A1D805lu, 0x73EDA753299D7D48lu};


	scalar_mult(x, y, z, ox, oy, oz, n);
	printf("%016lx", ox[5]);
	printf("%016lx", ox[4]);
	printf("%016lx", ox[3]);
	printf("%016lx", ox[2]);
	printf("%016lx", ox[1]);
	printf("%016lx", ox[0]);
	printf("\n");
	printf("%016lx", oy[5]);
	printf("%016lx", oy[4]);
	printf("%016lx", oy[3]);
	printf("%016lx", oy[2]);
	printf("%016lx", oy[1]);
	printf("%016lx", oy[0]);
	printf("\n");
	printf("%016lx", oz[5]);
	printf("%016lx", oz[4]);
	printf("%016lx", oz[3]);
	printf("%016lx", oz[2]);
	printf("%016lx", oz[1]);
	printf("%016lx", oz[0]);
	printf("\n");
}
