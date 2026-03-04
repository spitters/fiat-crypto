#import "G2.c"

void main() {
	printf("output is: \n");
	uint64_t ox[12];
	uint64_t oy[12];
	uint64_t oz[12];
    /* Coordinates of a point in Montgomery form, not sure why it outputs in plain form. */
	const uint64_t x[12] = {
          0xf5f28fa202940a10lu,
	  0xb3f5fb2687b4961alu,
	  0xa1a893b53e2ae580lu,
	  0x9894999d1a3caee9lu,
	  0x6f67b7631863366blu,
	  0x58191924350bcd7lu,
	  0xa5a9c0759e23f606lu,
	  0xaaa0c59dbccd60c3lu,
	  0x3bb17e18e2867806lu,
	  0x1b1ab6cc8541b367lu,
	  0xc2b6ed0ef2158547lu,
	  0x11922a097360edf3lu };
	const uint64_t y[12] = {
	  0x4c730af860494c4alu,
	  0x597cfa1f5e369c5alu,
	  0xe7e6856caa0a635alu,
	  0xbbefb5e96e0d495flu,
	  0x7d3a975f0ef25a2lu,
	  0x83fd8e7e80dae5lu,
	  0xadc0fc92df64b05dlu,
	  0x18aa270a2b1461dclu,
	  0x86adac6a3be4eba0lu,
	  0x79495c4ec93da33alu,
	  0xe7175850a43ccaedlu,
	  0xb2bc2a163de1bf2lu
	};
	const uint64_t z[12] = {
	  0x760900000002fffdlu,
	  0xebf4000bc40c0002lu,
	  0x5f48985753c758balu,
	  0x77ce585370525745lu,
	  0x5c071a97a256ec6dlu,
	  0x15f65ec3fa80e493lu,
	  0x0lu,
	  0x0lu,
	  0x0lu,
	  0x0lu,
	  0x0lu,
	  0x0lu
	};
	const uint64_t n[4] = {0xFFFFFFFF00000001lu, 0x53BDA402FFFE5BFElu, 0x3339D80809A1D805lu, 0x73EDA753299D7D48lu};

	scalar_mult(x, y, z, ox, oy, oz, n);
	printf("%016lx", ox[11]);
	printf("%016lx", ox[10]);
	printf("%016lx", ox[9]);
	printf("%016lx", ox[8]);
	printf("%016lx", ox[7]);
	printf("%016lx", ox[6]);
	printf("%016lx", ox[5]);
	printf("%016lx", ox[4]);
	printf("%016lx", ox[3]);
	printf("%016lx", ox[2]);
	printf("%016lx", ox[1]);
	printf("%016lx", ox[0]);
	printf("\n");
	printf("%016lx", oy[11]);
	printf("%016lx", oy[10]);
	printf("%016lx", oy[9]);
	printf("%016lx", oy[8]);
	printf("%016lx", oy[7]);
	printf("%016lx", oy[6]);
	printf("%016lx", oy[5]);
	printf("%016lx", oy[4]);
	printf("%016lx", oy[3]);
	printf("%016lx", oy[2]);
	printf("%016lx", oy[1]);
	printf("%016lx", oy[0]);
	printf("\n");
	printf("%016lx", oz[11]);
	printf("%016lx", oz[10]);
	printf("%016lx", oz[9]);
	printf("%016lx", oz[8]);
	printf("%016lx", oz[7]);
	printf("%016lx", oz[6]);
	printf("%016lx", oz[5]);
	printf("%016lx", oz[4]);
	printf("%016lx", oz[3]);
	printf("%016lx", oz[2]);
	printf("%016lx", oz[1]);
	printf("%016lx", oz[0]);
	printf("\n");
}
