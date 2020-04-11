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

// информация об инструкции
typedef struct {
	Blk *block;
	int block_index;
	int instruction_index;
} invariant_ins_t;

// массив информации об инвариантных инструкциях
typedef struct {
	invariant_ins_t *values;
	int size;
	int capacity;
} info_aray_t;

// массив блоков
typedef struct {
	Blk **blocks;
	int size;
	int capacity;
} block_array_t;

// получение имени по значению
char* get_name(Fn *fn, int val) {
	return val > Tmp0 ? fn->tmp[val].name : "[?]";
}

// вывод инструкции
void print_ins(Fn *fn, Ins ins) {
	char *to = get_name(fn, ins.to.val);
	char *arg0 = get_name(fn, ins.arg[0].val);
	char *arg1 = get_name(fn, ins.arg[1].val);

	printf("%s <- %s %s\n", to, arg0, arg1);
}

// вывод фи-функции
void print_phi(Fn *fn, Blk *blk) {
	printf("phi of %s:", blk->name);

	if (blk->phi) {
		char *to = blk->phi->to.val > Tmp0 ? fn->tmp[blk->phi->to.val].name : "[?]";
		printf("%s, narg: %d\n", to, blk->phi->narg);
	}
	else
		printf("NULL\n");
}

/***********************************************************************************************************/
// инициализация массива
info_aray_t init_array() {
	info_aray_t array;
	array.size = 0;
	array.capacity = 1;
	array.values = (invariant_ins_t *) malloc(sizeof(invariant_ins_t));
	return array;
}

// проверка наличия инструкции среди инвариантных
int contain_instruction(info_aray_t array, Ins *ins) {
	for (int i = 0; i < array.size; i++) {
		invariant_ins_t info = array.values[i];

		if (info.block->ins + info.instruction_index == ins)
			return 1;
	}

	return 0; // не содержится
}

// добавление в массив инвариантных блоков
void add_to_info_array(info_aray_t *array, Blk *block, int block_index, int instruction_index) {
	array->values[array->size].block = block;
	array->values[array->size].block_index = block_index;
	array->values[array->size].instruction_index = instruction_index;
	array->size++;

	if (array->size >= array->capacity) {
		array->capacity *= 2;
		array->values = (invariant_ins_t *) realloc(array->values, array->capacity * sizeof(invariant_ins_t));
	}
}

// вывод массива инвариантных инструкций
void print_info_array(Fn *fn, info_aray_t array) {
	for (int i = 0; i < array.size; i++) {
		Blk *blk = array.values[i].block;
		Ins ins = blk->ins[array.values[i].instruction_index];

		print_ins(fn, ins);
	}
}
/***********************************************************************************************************/
// инициализация массива блоков
block_array_t init_block_array() {
	block_array_t array;
	array.size = 0;
	array.capacity = 1;
	array.blocks = (Blk **) malloc(sizeof(Blk *));
	return array;
}

// проверка наличия блока в массиве
int contain_block(block_array_t array, Blk *blk) {
	for (int i = 0; i < array.size; i++)
		if (array.blocks[i] == blk)
			return 1;

	return 0;
}

// добавление блока во множество блоков
void add_to_block_array(block_array_t *array, Blk *blk) {
	if (contain_block(*array, blk))
		return;

	array->blocks[array->size++] = blk;

	if (array->size >= array->capacity) {
		array->capacity *= 2;
		array->blocks = (Blk **) realloc(array->blocks, array->capacity * sizeof(Blk *));
	}
}

/***********************************************************************************************************/

// получение блоков цикла
void get_loop_blocks(Blk *first, Blk *last, block_array_t *blocks) {
	add_to_block_array(blocks, first);

	if (first == last)
		return;

	if (first->s1->id > first->id)
		get_loop_blocks(first->s1, last, blocks);

	if (first->s2 && first->s2->id > first->id)
		get_loop_blocks(first->s2, last, blocks);
}

// проверка наличия достигающих определений внутри цикла
int have_reaching_definitions(block_array_t blocks, Ref arg) {
	for (int i = 0; i < blocks.size; i++)
		for (int j = 0; j < blocks.blocks[i]->nins; j++)
			if (blocks.blocks[i]->ins[j].to.val == arg.val) // нашли достигающее определение внутри цикла
				return 1;

	return 0; // не нашли достигающее определение
}

// достигающее определение помечено инвариантным
int is_reaching_definition_marked_invariant(info_aray_t invariant_instructions, Ref arg) {
	for (int i = 0; i < invariant_instructions.size; i++) {
		invariant_ins_t info = invariant_instructions.values[i];

		if (arg.val == info.block->ins[info.instruction_index].to.val)
			return 1;
	}

	return 0;
}

// проверка аргумента на инвариант цикла
int is_invariant_argument(block_array_t blocks, info_aray_t invariant_instructions, Ref arg, Blk *blk) {
	if (arg.type == RCon)
		return 1;

	for (Phi *p = blk->phi; p; p = p->link) {
		if (p->to.val != arg.val)
			continue;

		for (int i = 0; i < p->narg; i++)
			if (contain_block(blocks, p->blk[i]))
				return 0;

		return 1;
	}

	if (is_reaching_definition_marked_invariant(invariant_instructions, arg)) // если достигающее определение уже помечено инвариантным
		return 1;

	if (have_reaching_definitions(blocks, arg)) // если есть достигающее определение в цикле
		return 0; // то это не инвариантный аргумент

	return 1;
}

// проверка, что инструкция является инвариантом цикла (до этого ещё не просмотренным)
int is_new_invariant(block_array_t blocks, info_aray_t invariant_instructions, Ins *ins, Blk *blk) {
	if (!is_invariant_argument(blocks, invariant_instructions, ins->arg[0], blk))
		return 0;

	if (!is_invariant_argument(blocks, invariant_instructions, ins->arg[1], blk))
		return 0;

	return !contain_instruction(invariant_instructions, ins); // оба аргумента инвариантны, проверяем наличие
}

// получение инвариантных инструкций
info_aray_t get_invariant_instructions(Fn *fn, block_array_t blocks) {
	info_aray_t invariant_instructions = init_array();
	int was_added = 0;

	for (int i = 0; i < blocks.size; i++) {
		for (int j = 0; j < blocks.blocks[i]->nins; j++) {
			// printf("curr ins: ");
			// print_ins(fn, blocks.blocks[i]->ins[j]);

			if (is_new_invariant(blocks, invariant_instructions, blocks.blocks[i]->ins + j, blocks.blocks[i])) {
				add_to_info_array(&invariant_instructions, blocks.blocks[i], i, j);
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

// обновление предецессоров у предзаголовка
void update_prehead_pred(Blk *prehead, Blk *first, Blk *last) {
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
}

// обновление блоков функции
void update_fn(Fn *fn, Blk *prehead, Blk *first) {
	fn->nblk++;
	prehead->link = first;

	if (first == fn->start) {
		fn->start = prehead;
		return;
	}

	Blk *blk = fn->start; 

	while (blk->link != first)
		blk = blk->link;
	
	blk->link = prehead;
}

// создание предзаголовка
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

	update_prehead_pred(prehead, first, last);
	update_fn(fn, prehead, first);

	return prehead;
}

// можно ли перемещать инструкцию
int can_move(Fn *fn, invariant_ins_t info, Blk *last, block_array_t blocks) {
	for (int i = 0; i < blocks.size; i++)
		for (int j = 0; j < blocks.blocks[i]->nins; j++) {
			Ins *ins1 = blocks.blocks[i]->ins + j;
			Ins *ins2 = info.block->ins + info.instruction_index;
			
			if (ins1 != ins2 && ins1->to.val == ins2->to.val) {
				// printf("addresses: %p, %p\n", ins1, ins2);
				// printf("can not move: blk %s and %s: [%s] and [%s]\n", blocks.blocks[i]->name, block->name, get_name(fn, blocks.blocks[i]->ins[j].to.val), get_name(fn, block->ins[info.instruction_index].to.val));
				return 0;
			}
		}

	return dom(info.block, last); // TODO: &&... loop is...
}

// перемещение инвариантных инструкций
void move_instructions(Fn *fn, block_array_t blocks, Blk *prehead, Blk *last, info_aray_t invariant_instructions) {
	prehead->ins = (Ins *) malloc(invariant_instructions.size * sizeof(Ins)); // TODO: optimize memory
	prehead->nins = 0;

	Ins* blocks_ins[blocks.size];
	int blocks_ins_sizes[blocks.size];

	// копируем информацию об инструкциях в блоках
	for (int i = 0; i < blocks.size; i++) {
		blocks_ins_sizes[i] = blocks.blocks[i]->nins;
		blocks_ins[i] = (Ins *) malloc(blocks.blocks[i]->nins * sizeof(Ins));

		memcpy(blocks_ins[i], blocks.blocks[i]->ins, blocks.blocks[i]->nins * sizeof(Ins));
	}

	// пытаемся переместить инвариантные инструкции
	for (int i = 0; i < invariant_instructions.size; i++) {
		invariant_ins_t info = invariant_instructions.values[i];

		if (!can_move(fn, info, last, blocks))
			continue;

		prehead->ins[prehead->nins++] = info.block->ins[info.instruction_index];

		int index = --blocks_ins_sizes[info.block_index];

		for (int j = info.instruction_index; j < index; j++)
			blocks_ins[info.block_index][j] = blocks_ins[info.block_index][j + 1];
	}

	// обновляем массивы инструкций для блоков
	for (int i = 0; i < blocks.size; i++) {
		blocks.blocks[i]->nins = blocks_ins_sizes[i];
		blocks.blocks[i]->ins = blocks_ins[i];
	}
}

// обработка цикла
void process_loop(Fn *fn, Blk *first, Blk *last) {
	block_array_t blocks = init_block_array();
	get_loop_blocks(first, last, &blocks); // получаем блоки цикла

	// printf("loop blocks:\n");
	// for (int i = 0; i < blocks.size; i++) {
	// 	printf("%s\n", blocks.blocks[i]->name);
	// }

	info_aray_t invariant_instructions = get_invariant_instructions(fn, blocks); // получаем инвариантные инструкции

	// printf("All invariant_instructions:\n");
	// print_info_array(fn, invariant_instructions);

	if (invariant_instructions.size) { // если есть инвариантные инстркции
		Blk *prehead = make_prehead(fn, first, last); // вставляем предзаголовок
		move_instructions(fn, blocks, prehead, last, invariant_instructions); // перемещаем инвариантные инструкции
	}

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