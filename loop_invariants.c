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

int get_use_count(Fn *fn, int val) {
	return val > Tmp0 ? fn->tmp[val].nuse : -1;
}

// вывод инструкции
void print_ins(Fn *fn, Ins *ins) {
	if (!ins)
		printf("NULL\n");

	char *to = get_name(fn, ins->to.val);
	char *arg0 = get_name(fn, ins->arg[0].val);
	char *arg1 = get_name(fn, ins->arg[1].val);

	printf("%s <- %s %s\n", to, arg0, arg1);
}

// вывод фи-функции
void print_phi(Fn *fn, Phi *phi) {
	if (phi) {
		printf("%s, narg: %d\n", get_name(fn, phi->to.val), phi->narg);
	}
	else
		printf("NULL\n");
}

void print_use_info(Fn *fn, int val) {
	printf("    name: %s\n", get_name(fn, val));
	printf("    count: %d\n", get_use_count(fn, val));

	if (get_use_count(fn, val) == -1)
		return;

	for (int i = 0; i < fn->tmp[val].nuse; i++) {
		Use *use = fn->tmp[val].use + i;

		printf("    use[%d]: blkid: %d   ", i, use->bid);
		if (use->type == UPhi) {
			printf("UPhi\t");
			Phi *phi = (Phi *) use->u.phi;
			print_phi(fn, phi);
		}
		else if (use->type == UIns) {
			printf("UIns\t");
			Ins *ins = (Ins *) use->u.ins;
			print_ins(fn, ins);
		}
		else if (use->type == UXXX){
			printf("UXXX [?]\n");
		}
		else if (use->type == UJmp){
			printf("Ujmp [?]\n");
		}
	}
}

void print_all_use(Fn *fn) {
	printf("Print use:\n");
	Blk *blk = fn->start;

	for (int i = 0; i < fn->nblk; i++) {
		printf("@%s:\n", blk->name);

		for (int j = 0; j < blk->nins; j++) {
			Ins ins = blk->ins[j];
			print_use_info(fn, ins.to.val);
			// printf("    ");
			// printf("%s: %d\t", get_name(fn, ins.to.val), get_use_count(fn, ins.to.val));
			// printf("%s: %d\t", get_name(fn, ins.arg[0].val), get_use_count(fn, ins.arg[0].val));
			// printf("%s: %d\n", get_name(fn, ins.arg[1].val), get_use_count(fn, ins.arg[1].val));			
		}

		blk = blk->link;
	}
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
		Ins *ins = blk->ins + array.values[i].instruction_index;

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
void get_loop_blocks(Blk *last, Blk *curr, block_array_t *blocks) {
	add_to_block_array(blocks, curr);

	if (last->s1 == curr || last->s2 == curr)
		return;

	for (int i = 0; i < curr->npred; i++)
		if (curr->pred[i]->id < curr->id)
			get_loop_blocks(last, curr->pred[i], blocks);
}

// все достигающие определения вне цикла
int are_reaching_definitions_out_of_loop(Fn *fn, block_array_t blocks, Ref arg) {
	for (int k = 0; k < blocks.size; k++) {
		for (Phi *phi = blocks.blocks[k]->phi; phi; phi = phi->link) {
			// printf("check phi: ");
			// print_phi(fn, phi);

			if (phi->to.val != arg.val)
				continue;

			for (int i = 0; i < phi->narg; i++) {
				// printf("    Check block @%s    ", phi->blk[i]->name);

				if (contain_block(blocks, phi->blk[i])) {
					// printf("block EST\n");
					return 0;
				}

				// printf("blocka NET\n");
			}
		}		
	}
	
	return 1;
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
int is_invariant_argument(Fn *fn, block_array_t blocks, info_aray_t invariant_instructions, Ref arg, Blk *blk) {
	if (arg.type == RCon) {
		// printf("this is const\n");
		return 1;
	}

	if (!are_reaching_definitions_out_of_loop(fn, blocks, arg))
		return 0;

	if (is_reaching_definition_marked_invariant(invariant_instructions, arg)) // если достигающее определение уже помечено инвариантным
		return 1;

	if (have_reaching_definitions(blocks, arg)) // если есть достигающее определение в цикле
		return 0; // то это не инвариантный аргумент

	return 1;
}

// проверка, что инструкция является инвариантом цикла (до этого ещё не просмотренным)
int is_new_invariant(Fn *fn, block_array_t blocks, info_aray_t invariant_instructions, Ins *ins, Blk *blk) {
	// printf("Check is invariant: ");
	// print_ins(fn, ins);
	
	// printf("Check arg[0]:\n");
	if (!is_invariant_argument(fn, blocks, invariant_instructions, ins->arg[0], blk))
		return 0;

	// printf("Check arg[1]:\n");
	if (!is_invariant_argument(fn, blocks, invariant_instructions, ins->arg[1], blk))
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
			// print_ins(fn, blocks.blocks[i]->ins + j);

			if (is_new_invariant(fn, blocks, invariant_instructions, blocks.blocks[i]->ins + j, blocks.blocks[i])) {
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
void update_pred(Blk **preds, int npreds, Blk *prehead, Blk *first, Blk *last) {
	Blk **prehead_preds = (Blk **) malloc(npreds * sizeof(Blk *));
	Blk **first_preds = (Blk **) malloc(npreds * sizeof(Blk *));

	int index1 = 0;
	int index2 = 0;

	first_preds[index1++] = prehead;

	for (int i = 0; i < npreds; i++) {
		if (preds[i]->id >= first->id) {
			first_preds[index1++] = preds[i];
		}
		else {
			if (preds[i]->s1 == first)
				preds[i]->s1 = prehead;

			if (preds[i]->s2 == first)
				preds[i]->s2 = prehead;

			prehead_preds[index2++] = preds[i];
		}
	}

	first->pred = first_preds;
	first->npred = index1;
	prehead->pred = prehead_preds;
	prehead->npred = index2;
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

	if (!strcmp(first->pred[0]->name, prehead->name)) {
		free(prehead);
		return first->pred[0];
	}

	prehead->s1 = first;
	prehead->s2 = NULL;
	prehead->jmp.type = Jjmp;

	update_pred(first->pred, first->npred, prehead, first, last);
	update_fn(fn, prehead, first);

	prehead->ins = NULL;
	prehead->nins = 0;

	return prehead;
}

// есть ли ещё одно определение
int has_another_def(Blk *blk, Ins *ins) {
	for (Phi *phi = blk->phi; phi; phi = phi->link)
		if (phi->to.val == ins->to.val)
			return 1;

	for (int i = 0; i < blk->nins; i++)
		if (blk->ins + i != ins && blk->ins[i].to.val == ins->to.val)
			return 1;

	return 0;
}

// можно ли перемещать инструкцию
int can_move(Fn *fn, invariant_ins_t info, Blk *last, block_array_t blocks) {
	Ins *ins = info.block->ins + info.instruction_index;

	for (int i = 0; i < blocks.size; i++)
		if (has_another_def(blocks.blocks[i], ins))
			return 0;

	if (dom(info.block, last))
		return 1;

	int val = ins->to.val;
	for (int i = 0; i < fn->tmp[val].nuse; i++) {
		Use *use = fn->tmp[val].use + i;

		if (use->bid <= last->id)
			return 0;
	}

	return 1;
}

// перемещение инвариантных инструкций
void move_instructions(Fn *fn, block_array_t blocks, Blk *prehead, Blk *last, info_aray_t invariant_instructions) {
	prehead->ins = (Ins *) realloc(prehead->ins, (prehead->nins + invariant_instructions.size) * sizeof(Ins)); // TODO: optimize memory
	
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
	get_loop_blocks(last, last, &blocks); // получаем блоки цикла

	for (int i = 0, j = blocks.size - 1; i < j; i++, j--) {
		Blk *tmp = blocks.blocks[i];
		blocks.blocks[i] = blocks.blocks[j];
		blocks.blocks[j] = tmp;
	}
	
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

void process_as_possible_footer(Fn *fn, Blk *blk) {
	Blk **pred = blk->pred;

	if (blk->s1->id <= blk->id) {
		process_loop(fn, blk->s1, blk);
		return;
	}
	
	assert(blk->s2 && blk->s2->id <= blk->id);
	process_loop(fn, blk->s2, blk);
	// for (int i = 0; i < blk->npred; i++)
	// 	if (blk->id <= pred[i]->id)
	// 		process_loop(fn, blk, pred[i]);
}

static void readfn (Fn *fn) {
    fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
    fillpreds(fn);
    filluse(fn);
    ssa(fn); 
    filluse(fn);

    // print_all_use(fn);

    block_array_t lasts = init_block_array();

	for (Blk *blk = fn->start; blk; blk = blk->link) {
		for (int i = 0; i < blk->npred; i++)
			if (blk->id <= blk->pred[i]->id)
				add_to_block_array(&lasts, blk->pred[i]);
	}

	for (int i = 0; i < lasts.size; i++)
		process_as_possible_footer(fn, lasts.blocks[i]); // TODO: FIX THIS

    printfn(fn, stdout);
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}