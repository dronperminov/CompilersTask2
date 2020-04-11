#ifdef __cplusplus
#define export exports
extern "C" {
#include <qbe/all.h>
}
#undef export
#else
#include <qbe/all.h>
#endif

#include <stdio.h>

typedef struct instruction_info {
	Blk *block;
	int instruction_index;
} instruction_info_t;

typedef struct array {
	instruction_info_t *values;
	int size;
	int capacity;
} array_t;

typedef struct block_array {
	Blk **blocks;
	int size;
	int capacity;
} block_array_t;

// инициализация массива
array_t init_array() {
	array_t array;
	array.size = 0;
	array.capacity = 1;
	array.values = (instruction_info_t *) malloc(sizeof(instruction_info_t));
	return array;
}

block_array_t init_block_array() {
	block_array_t array;
	array.size = 0;
	array.capacity = 1;
	array.blocks = (Blk **) malloc(sizeof(Blk *));
	return array;
}

void add_to_array(array_t *array, instruction_info_t info) {
	array->values[array->size++] = info;

	if (array->size >= array->capacity) {
		array->capacity *= 2;
		array->values = (instruction_info_t *) realloc(array->values, array->capacity * sizeof(instruction_info_t));
	}
}

void add_to_block_array(block_array_t *array, Blk *blk) {
	for (int i = 0; i < array->size; i++)
		if (array->blocks[i] == blk)
			return;

	array->blocks[array->size++] = blk;

	if (array->size >= array->capacity) {
		array->capacity *= 2;
		array->blocks = (Blk **) realloc(array->blocks, array->capacity * sizeof(Blk *));
	}
}

int is_invariant_argument(block_array_t blocks, array_t invariant_instructions, Ref arg, Blk *blk) {
	if (arg.type == RCon)
		return 1;

	for (Phi *p = blk->phi; p; p = p->link) {
		if (p->to.val != arg.val)
			continue;

		for (int i = 0; i < p->narg; i++)
			for (int j = 0; j < blocks.size; j++)
				if (p->blk[i] == blocks.blocks[j])
					return 0;

		return 1;
	}

	for (int i = 0; i < invariant_instructions.size; i++) {
		instruction_info_t info = invariant_instructions.values[i];
		Ins ins = info.block->ins[info.instruction_index];

		if (arg.val == ins.to.val)
			return 1;
	}

	for (int i = 0; i < blocks.size; i++)
		for (int j = 0; j < blocks.blocks[i]->nins; j++)
			if (blocks.blocks[i]->ins[j].to.val == arg.val)
				return 0;

	return 1;
}

int is_new_invariant(block_array_t blocks, array_t invariant_instructions, Ins *ins, Blk *blk) {
	if (!is_invariant_argument(blocks, invariant_instructions, ins->arg[0], blk))
		return 0;

	if (!is_invariant_argument(blocks, invariant_instructions, ins->arg[1], blk))
		return 0;

	for (int i = 0; i < invariant_instructions.size; i++) {
		Blk *blk = invariant_instructions.values[i].block;
		int index = invariant_instructions.values[i].instruction_index;

		if (blk->ins + index == ins)
			return 0;
	}

	return 1;
}

char* get_name(Fn *fn, int val) {
	return val > Tmp0 ? fn->tmp[val].name : "[?]";
}

void print_ins(Fn *fn, Ins ins) {
	char *to = get_name(fn, ins.to.val);
	char *arg0 = get_name(fn, ins.arg[0].val);
	char *arg1 = get_name(fn, ins.arg[1].val);

	printf("%s <- %s %s\n", to, arg0, arg1);
}

void print_phi(Fn *fn, Blk *blk) {
	printf("phi of %s:", blk->name);

	if (blk->phi) {
		char *to = blk->phi->to.val > Tmp0 ? fn->tmp[blk->phi->to.val].name : "[?]";
		printf("%s, narg: %d\n", to, blk->phi->narg);
	}
	else
		printf("NULL\n");
}

void print_array(Fn *fn, array_t array) {
	for (int i = 0; i < array.size; i++) {
		Blk *blk = array.values[i].block;
		Ins ins = blk->ins[array.values[i].instruction_index];

		print_ins(fn, ins);
	}
}

void get_loop_blocks(Blk *first, Blk *last, block_array_t *blocks) {
	add_to_block_array(blocks, first);

	if (first == last)
		return;

	if (first->s1->id > first->id)
		get_loop_blocks(first->s1, last, blocks);
	
	if (first->s2 && first->s2->id > first->id)
		get_loop_blocks(first->s2, last, blocks);
}

Blk* make_prehead(Fn *fn, Blk *first, Blk *last) {
	Blk *prehead = (Blk *) calloc(1, sizeof(Blk));
	
	strcpy(prehead->name, "prehead@");
	strcat(prehead->name, first->name);

	prehead->s1 = first;
	prehead->s2 = NULL;
	prehead->jmp.type = Jjmp;

	prehead->pred = first->pred;
	prehead->npred = first->npred;

	first->pred = (Blk **) malloc(2 * sizeof(Blk *));
	first->pred[0] = prehead;
	first->pred[1] = last;
	first->npred = 2;

	int index = 0;
	for (int i = 0; i < prehead->npred; i++) {
		if (prehead->pred[i] == last)
			continue;

		if (prehead->pred[i]->s1 == first)
			prehead->pred[i]->s1 = prehead;

		if (prehead->pred[i]->s2 == first)
			prehead->pred[i]->s2 = prehead;

		prehead->pred[index++] = prehead->pred[i];
	}

	prehead->npred = index;

	fn->nblk++;
	prehead->link = first;

	if (first == fn->start) {
		fn->start = prehead;
		return prehead;
	}

	Blk *blk = fn->start; 

	while (blk->link != first)
		blk = blk->link;
	
	blk->link = prehead;
	return prehead;
}

array_t get_invariant_instructions(Fn *fn, block_array_t blocks) {
	array_t invariant_instructions = init_array();

	// printf("first: %s, last: %s\n", first->name, last->name);
	int was_added = 0;

	for (int i = 0; i < blocks.size; i++) {
		Blk *blk = blocks.blocks[i];

		for (int j = 0; j < blk->nins; j++) {
			// printf("curr ins: ");
			// print_ins(fn, blk->ins[j]);

			if (is_new_invariant(blocks, invariant_instructions, blk->ins + j, blk)) {
				instruction_info_t info;
				info.block = blk;
				info.instruction_index = j;
				add_to_array(&invariant_instructions, info);
				was_added = 1;
			}
		}

		if (i == blocks.size - 1 && was_added) {
			i = -1;
			was_added = 0;
		}
	}

	return invariant_instructions;
}

int can_move(Fn *fn, instruction_info_t info, Blk *last, block_array_t blocks) {
	Blk *block = info.block;

	for (int i = 0; i < blocks.size; i++)
		for (int j = 0; j < blocks.blocks[i]->nins; j++) {
			Ins *ins1 = blocks.blocks[i]->ins + j;
			Ins *ins2 = block->ins + info.instruction_index;
			
			if (ins1 != ins2 && ins1->to.val == ins2->to.val) {
				// printf("addresses: %p, %p\n", ins1, ins2);
				// printf("can not move: blk %s and %s: [%s] and [%s]\n", blocks.blocks[i]->name, block->name, get_name(fn, blocks.blocks[i]->ins[j].to.val), get_name(fn, block->ins[info.instruction_index].to.val));
				return 0;
			}
		}

	return dom(block, last); // TODO: &&... loop is...
}

Ins remove_ins(instruction_info_t info) {
	Ins ins = info.block->ins[info.instruction_index];
	info.block->nins--;

	for (int i = info.instruction_index; i < info.block->nins; i++)
		info.block->ins[i] = info.block->ins[i + 1];

	return ins;
}

int blk2idx(Blk *blk, block_array_t blocks) {
	for (int i = 0; i < blocks.size; i++)
		if (blk == blocks.blocks[i])
			return i;

	return -1;
}

void move_instructions(Fn *fn, block_array_t blocks, Blk *prehead, Blk *last, array_t invariant_instructions) {
	prehead->ins = (Ins *) malloc(invariant_instructions.size * sizeof(Ins)); // TODO: optimize memory
	prehead->nins = 0;

	Ins* blocks_ins[blocks.size];
	int blocks_ins_sizes[blocks.size];

	for (int i = 0; i < blocks.size; i++) {
		blocks_ins[i] = (Ins *) malloc(blocks.blocks[i]->nins * sizeof(Ins));

		memcpy(blocks_ins[i], blocks.blocks[i]->ins, blocks.blocks[i]->nins * sizeof(Ins));
		blocks_ins_sizes[i] = blocks.blocks[i]->nins;
	}

	for (int i = 0; i < invariant_instructions.size; i++) {
		instruction_info_t info = invariant_instructions.values[i];
		int block_index = blk2idx(info.block, blocks);

		if (can_move(fn, invariant_instructions.values[i], last, blocks)) {
			prehead->ins[prehead->nins++] = info.block->ins[info.instruction_index];

			int index = --blocks_ins_sizes[block_index];

			for (int j = info.instruction_index; j < index; j++)
				blocks_ins[block_index][j] = blocks_ins[block_index][j + 1];
		}
	}

	for (int i = 0; i < blocks.size; i++) {
		blocks.blocks[i]->nins = blocks_ins_sizes[i];
		blocks.blocks[i]->ins = blocks_ins[i];
	}
}

void process_loop(Fn *fn, Blk *first, Blk *last) {
	block_array_t blocks = init_block_array();
	get_loop_blocks(first, last, &blocks);

	// printf("loop blocks:\n");
	// for (int i = 0; i < blocks.size; i++) {
	// 	printf("%s\n", blocks.blocks[i]->name);
	// }

	array_t invariant_instructions = get_invariant_instructions(fn, blocks);

	// printf("All invariant_instructions:\n");
	// print_array(fn, invariant_instructions);

	if (invariant_instructions.size == 0) {
		free(invariant_instructions.values);
		return;
	}
	
	Blk *prehead = make_prehead(fn, first, last);

	move_instructions(fn, blocks, prehead, last, invariant_instructions);

	free(invariant_instructions.values);
	free(blocks.blocks);
}

void process_as_possible_loop_header(Fn *fn, Blk *blk) {
	Blk **pred = blk->pred;

	for (int i = 0; i < blk->npred; i++)
		if (blk->id <= pred[i]->id)
			process_loop(fn, blk, pred[i]);
}

static void readfn (Fn *fn) {
    fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
    fillpreds(fn);
    filluse(fn);
    ssa(fn); 

	for (Blk *blk = fn->start; blk; blk = blk->link) {
		// print_phi(fn, blk);
		process_as_possible_loop_header(fn, blk); // TODO: FIX THIS
	}

    printfn(fn, stdout);
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}