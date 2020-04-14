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

// #define PRINT_LASTS 1
// #define PRINT_LASTS_BLOCKS 1

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
	uint max_id;
	int size;
	int capacity;
} block_array_t;

/*********************************** Печать ***********************************/

// вывод имени с фи-суффиксом
void print_arg(Fn *fn, Ref arg) {
	if (arg.val >= Tmp0) {
		printf("[%d]%s.%d", arg.val, fn->tmp[arg.val].name, fn->tmp[arg.val].phi);
	}
	else if (arg.type == RCon) {
		printf("Const");
	}
	else if (arg.val == RXX) {
		printf("[RXX]");
	}
	else {
		printf("[Ref]");
	}
}

// вывод инструкции
void print_ins(Fn *fn, Ins *ins) {
	if (!ins) {
		printf("\t[Null Ins]\n");
		return;
	}

	printf("\t");
	print_arg(fn, ins->to);
	printf(" = [Op] ");
	print_arg(fn, ins->arg[0]);
	printf(", ");
	print_arg(fn, ins->arg[1]);
	printf("\n");
}

// вывод фи-функции
void print_phi(Fn *fn, Phi *phi) {
	if (!phi) {
		printf("\t[Null Phi]\n");
		return;
	}

	printf("\t");
	print_arg(fn, phi->to);
	printf(" = phi @%s ", phi->blk[0]->name);
	print_arg(fn, phi->arg[0]);
	for (int i = 1; i < phi->narg; i++) {
		printf(", @%s ", phi->blk[i]->name);
		print_arg(fn, phi->arg[i]);
	}
	printf("\n");
}

void print_block(Fn *fn, Blk *blk) {
	if (!blk) {
		printf("[Null Blk]\n");
		return;
	}

	printf("@%s (id:%d):\n", blk->name, blk->id);
	for (Phi *phi = blk->phi; phi; phi = phi->link) {
		print_phi(fn, phi);
	}
	for (Ins *ins = blk->ins; ins < blk->ins + blk->nins; ins++) {
		print_ins(fn, ins);
	}
	// print_jmp(blk->jmp);
}

void print_use_info(Fn *fn, Ref arg) {
	printf("Uses of ");
	print_arg(fn, arg);

	if (arg.val < Tmp0) {
		printf(": –\n");
		return;
	}

	Tmp tmp = fn->tmp[arg.val];
	printf(": %d\n", tmp.nuse);

	for (int i = 0; i < tmp.nuse; i++) {
		Use *use = tmp.use + i;

		printf("\tuse[%d] in blk %d: ", i, use->bid);
		if (use->type == UPhi) {
			printf("(UPhi) ");
			Phi *phi = (Phi *) use->u.phi;
			print_phi(fn, phi);
		}
		else if (use->type == UIns) {
			printf("(UIns) ");
			Ins *ins = (Ins *) use->u.ins;
			print_ins(fn, ins);
		}
		else if (use->type == UXXX){
			printf("[UXXX]\n");
		}
		else if (use->type == UJmp){
			printf("[Ujmp]\n");
		}
	}
}

void print_all_use(Fn *fn) {
	printf("All uses for each definition in function:\n");
	Blk *blk = fn->start;

	for (int i = 0; i < fn->nblk; i++) {
		printf("For definitions in @%s:\n", blk->name);

		for (int j = 0; j < blk->nins; j++) {
			Ins ins = blk->ins[j];
			print_use_info(fn, ins.to);
		}

		blk = blk->link;
	}
}

/********** Функции для работы с массивом инвариантных инструкций *************/
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

/******************* Функции для работы с массивом блоков *********************/
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
int add_to_block_array(block_array_t *array, Blk *blk) {
	if (contain_block(*array, blk))
		return 0;

	array->blocks[array->size] = blk;

	if (blk->id > array->max_id)
		array->max_id = blk->id;

	array->size++;

	if (array->size >= array->capacity) {
		array->capacity *= 2;
		array->blocks = (Blk **) realloc(array->blocks, array->capacity * sizeof(Blk *));
	}

	return 1;
}

// обмен местами двух блоков в массиве
void swap_block_array(block_array_t array, int i, int j) {
	Blk *tmp = array.blocks[i];
	array.blocks[i] = array.blocks[j];
	array.blocks[j] = tmp;
}

void sort_blocks_array_by_id(block_array_t array) {
	int is_sorted = 0;

	while (!is_sorted) {
		is_sorted = 1;

		for (int i = 0; i < array.size - 1; i++) {
			if (array.blocks[i]->id < array.blocks[i + 1]->id) {
				is_sorted = 0;
				swap_block_array(array, i, i + 1);
			}
		}
	}
}

void print_block_array(block_array_t array) {
	for (int i = 0; i < array.size; i++) {
		printf("@%s (id: %d)\n", array.blocks[i]->name, array.blocks[i]->id);
	}
}

/****************** Проверка направления дуги между блоками *******************/

int is_forward_edge(Blk *a, Blk *b) {
	assert(a->s1 == b || a->s2 == b);

	if (a->id && b->id)
		return a->id < b->id;

	return a->id == 0;
}

int is_backward_edge(Blk *a, Blk *b) {
	assert(a->s1 == b || a->s2 == b);

	if (a->id && b->id)
		return a->id >= b->id;

	return 0;
}

/********************* Получение инвариантных инструкций **********************/

// если есть несколько достигающих определений, и одно
// из них внутри цикла, то переменная не инвариантна
int check_for_multiple_definitions(Fn *fn, block_array_t blocks, Ref arg) {
	for (int k = 0; k < blocks.size; k++) {
		for (Phi *phi = blocks.blocks[k]->phi; phi; phi = phi->link) {

			if (phi->to.val != arg.val)
				continue;

			// TODO: должны проверяться не блоки из которых приходит
			// определение, а блоки в которых определение находится?
			for (int i = 0; i < phi->narg; i++)
				if (contain_block(blocks, phi->blk[i]))
					return 0;

			return 1;
		}
	}

	return -1;
}

// проверка наличия достигающего определения внутри цикла
int is_definition_in_loop_instructions(block_array_t blocks, Ref arg) {
	for (int i = 0; i < blocks.size; i++)
		for (int j = 0; j < blocks.blocks[i]->nins; j++)
			if (blocks.blocks[i]->ins[j].to.val == arg.val)
				return 1;

	return 0; // не нашли достигающее определение внутри цикла
}

// достигающее определение помечено инвариантным
int is_definition_marked_invariant(info_aray_t invariant_instructions, Ref arg) {
	for (int i = 0; i < invariant_instructions.size; i++) {
		invariant_ins_t info = invariant_instructions.values[i];

		if (arg.val == info.block->ins[info.instruction_index].to.val)
			return 1;
	}

	return 0;
}

// проверка аргумента на инвариант цикла
int is_invariant_argument(Fn *fn, block_array_t blocks, info_aray_t invariant_instructions, Ref arg, Blk *blk) {
	// константа инвариантна
	if (arg.type == RCon)
		return 1;

	// переменная не может быть инвариантна, если достигающих
	// определений несколько и одно из них внутри цикла
	int phi = check_for_multiple_definitions(fn, blocks, arg);

	if (phi == 1) // определений несколько, все вне цикла
		return 1;

	if (phi == 0) // определений несколько, одно из цикла
		return 0;
	// есть одно определение

	// переменная инвариантна, если среди инструкций цикла нет её определения
	if (!is_definition_in_loop_instructions(blocks, arg))
		return 1;

	// переменная определена инструкцией внутри цикла

	// переменная инвариантна, если достигающее определение уже помечено инвариантным
	return is_definition_marked_invariant(invariant_instructions, arg);
}

// проверка, что инструкция является инвариантом цикла (до этого ещё не добавленым)
int is_new_invariant(Fn *fn, block_array_t blocks, info_aray_t invariant_instructions, Ins *ins, Blk *blk) {
	// если уже есть в инвариантах, то это не новый инвариант
	if (contain_instruction(invariant_instructions, ins))
		return 0;

	// инструкция – инвариант цикла, только если оба аргумента инвариантны
	if (!is_invariant_argument(fn, blocks, invariant_instructions, ins->arg[0], blk))
		return 0;

	if (!is_invariant_argument(fn, blocks, invariant_instructions, ins->arg[1], blk))
		return 0;

	return 1;
}

// собираем все инвариантные инструкции цикла
info_aray_t get_invariant_instructions(Fn *fn, block_array_t blocks) {
	info_aray_t invariant_instructions = init_array();
	int was_added = 1;

	while (was_added) {
		was_added = 0;

		for (int i = 0; i < blocks.size; i++) {
			for (int j = 0; j < blocks.blocks[i]->nins; j++) {
				if (is_new_invariant(fn, blocks, invariant_instructions, blocks.blocks[i]->ins + j, blocks.blocks[i])) {
					add_to_info_array(&invariant_instructions, blocks.blocks[i], i, j);
					was_added = 1;
				}
			}
		}
	}

	return invariant_instructions;
}

/*************************** Создание предзаголовка ***************************/

// обновление предецессоров у предзаголовка и заголовка
void update_pred(Blk **preds, int npreds, Blk *prehead, Blk *first) {
	Blk **prehead_preds = (Blk **) alloc(npreds * sizeof(Blk *));
	Blk **first_preds = (Blk **) alloc(npreds * sizeof(Blk *));

	int index1 = 0;
	int index2 = 0;

	// дуга из предзаголовка в заголовок
	first_preds[index1++] = prehead;

	for (int i = 0; i < npreds; i++) {
		// оставляем обратно направленные дуги заголовку
		if (is_backward_edge(preds[i], first)) {
			first_preds[index1++] = preds[i];
		}
		else {
			// перевязываем прямые дуги с заголовка на предзаголовок
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
Blk* make_prehead(Fn *fn, Blk *first) {
	Blk *prehead = (Blk *) alloc(sizeof(Blk));

	strcpy(prehead->name, "prehead@");
	strcat(prehead->name, first->name);

	// если предзаголовок уже был создан, то возвращаем его
	for (int i = 0; i < first->npred; i++)
		if (!strcmp(first->pred[i]->name, prehead->name))
			return first->pred[i];

	// добавляем все связи между блоками
	prehead->s1 = first;
	prehead->s2 = NULL;
	prehead->jmp.type = Jjmp;

	update_pred(first->pred, first->npred, prehead, first);
	update_fn(fn, prehead, first);

	// пока предзаголовок пустой
	prehead->ins = NULL;
	prehead->nins = 0;

	return prehead;
}

/******************** Перемещение инвариантных инструкций *********************/

// если определение в блоке, доминирующем все
// выходы из цикла, то его можно перенести
int dominates_exits(block_array_t blocks, Blk *block) {
	for (int i = 0; i < blocks.size; i++) {
		// блоки без выхода из цикла пропускаем
		if (!blocks.blocks[i]->s2 || contain_block(blocks, blocks.blocks[i]->s2))
			continue;

		if (!dom(block, blocks.blocks[i]))
			return 0;
	}

	return 1;
}

// используется ли переменная после цикла
int has_use_after_loop(Fn *fn, uint max_id, int val) {
	for (int i = 0; i < fn->tmp[val].nuse; i++)
		if (fn->tmp[val].use[i].bid > max_id)
			return 1;

	return 0;
}

// можно ли переместить инструкцию
int can_move(Fn *fn, invariant_ins_t info, block_array_t blocks) {
	Ins *ins = info.block->ins + info.instruction_index;

	// определение нельзя перенести, если в цикле есть ещё одно определение
	// этой же переменной; но ssa-форма делает определения независимыми, поэтому
	// нет необходимости это проверять

	// определение можно перенести если оно в блоке,
	// доминирующем все выходы из цикла...
	if (dominates_exits(blocks, info.block))
		return 1;

	// ...или мертво после цикла (нет использований)
	if (!has_use_after_loop(fn, blocks.max_id, ins->to.val))
		return 1;

	return 0;
}

// перемещение инвариантных инструкций
void move_instructions(Fn *fn, block_array_t blocks, Blk *prehead, Blk *last, info_aray_t invariant_instructions) {
	Ins *prehead_ins = (Ins *) alloc((prehead->nins + invariant_instructions.size) * sizeof(Ins));
	memcpy(prehead_ins, prehead->ins, prehead->nins * sizeof(Ins));
	prehead->ins = prehead_ins;

	Ins* blocks_ins[blocks.size];
	int blocks_ins_sizes[blocks.size];

	// копируем информацию об инструкциях в блоках
	// в новые массивы, которые и будем менять,
	// и находим максимальный ид. среди блоков цикла
	for (int i = 0; i < blocks.size; i++) {
		blocks_ins_sizes[i] = blocks.blocks[i]->nins;
		blocks_ins[i] = (Ins *) alloc(blocks.blocks[i]->nins * sizeof(Ins));

		memcpy(blocks_ins[i], blocks.blocks[i]->ins, blocks.blocks[i]->nins * sizeof(Ins));
	}

	// пытаемся переместить инвариантные инструкции
	for (int i = 0; i < invariant_instructions.size; i++) {
		invariant_ins_t info = invariant_instructions.values[i];

		// некоторые инструкции нельзя перенести
		if (!can_move(fn, info, blocks))
			continue;

		// добавляем инструкцию в предзаголовок
		prehead->ins[prehead->nins++] = info.block->ins[info.instruction_index];

		// удаляем изнутри цикла
		int shift = info.block->nins - blocks_ins_sizes[info.block_index];
		int end_index = --blocks_ins_sizes[info.block_index];

		for (int j = info.instruction_index - shift; j < end_index; j++)
			blocks_ins[info.block_index][j] = blocks_ins[info.block_index][j + 1];
	}

	// обновляем массивы инструкций для блоков
	for (int i = 0; i < blocks.size; i++) {
		blocks.blocks[i]->nins = blocks_ins_sizes[i];
		blocks.blocks[i]->ins = blocks_ins[i];
	}
}

/****************************** Обработка цикла *******************************/
// получение блоков, однозначно являющихся выходами циклов
block_array_t get_lasts(Fn *fn) {
	block_array_t lasts = init_block_array();

	for (Blk *blk = fn->start; blk; blk = blk->link)
		for (int i = 0; i < blk->npred; i++)
			if (is_backward_edge(blk->pred[i], blk))
				add_to_block_array(&lasts, blk->pred[i]);

	return lasts;
}

// получение блоков цикла
void get_loop_blocks(Blk *last, Blk *curr, block_array_t *blocks) {
	if (!add_to_block_array(blocks, curr))
		return;

	if ((last->s1 == curr || last->s2 == curr) && is_backward_edge(last, curr))
		return;

	for (int i = 0; i < curr->npred; i++)
		if (curr->pred[i]->id != curr->id)
			get_loop_blocks(last, curr->pred[i], blocks);
}

// обработка цикла
void process_loop(Fn *fn, Blk *first, Blk *last, block_array_t blocks) {
	for (int i = 0, j = blocks.size - 1; i < j; i++, j--) {
		Blk *tmp = blocks.blocks[i];
		blocks.blocks[i] = blocks.blocks[j];
		blocks.blocks[j] = tmp;
	}

	// находим инвариантные инструкции
	info_aray_t invariant_instructions = get_invariant_instructions(fn, blocks);

	// вставляем и заполняем предзаголовок только если есть инварианты
	if (invariant_instructions.size) {
		Blk *prehead = make_prehead(fn, first);
		move_instructions(fn, blocks, prehead, last, invariant_instructions);
	}

	free(invariant_instructions.values);
	free(blocks.blocks);
}

// по блоку, из которого обратная дуга, находим цикл и обрабатываем его
void process_as_footer(Fn *fn, Blk *blk) {
	// находим блоки цикла
	block_array_t blocks = init_block_array();
	get_loop_blocks(blk, blk, &blocks);

#ifdef PRINT_LASTS_BLOCKS
	printf("Loop for last @%s:\n", blk->name);
	print_block_array(blocks);
#endif

	// подставляем заголовок и обрабатываем цикл
	// заголовок -- блок, в который идёт обратная дуга
	if (is_backward_edge(blk, blk->s1)) {
		process_loop(fn, blk->s1, blk, blocks);
		return;
	}

	assert(is_backward_edge(blk, blk->s2));
	process_loop(fn, blk->s2, blk, blocks);
}

/*********************** Удаление пустых предзаголовков ***********************/

void remove_prehead(Fn *fn, Blk *prehead) {
	Blk *head = prehead->s1;

	for (int i = 0; i < prehead->npred; i++) {
		if (prehead->pred[i]->s1 == prehead)
			prehead->pred[i]->s1 = head;

		if (prehead->pred[i]->s2 == prehead)
			prehead->pred[i]->s2 = head;

		head->pred[i ? head->npred++ : 0] = prehead->pred[i];
	}

	fn->nblk--;

	if (prehead == fn->start) {
		fn->start = prehead->link;
		return;
	}

	Blk *blk = fn->start;

	while (blk->link != prehead)
		blk = blk->link;

	blk->link = prehead->link;
}

void remove_empty_preheads(Fn *fn) {
	for (Blk *blk = fn->start; blk; blk = blk->link)
		if (!strncmp("prehead@", blk->name, 8) && blk->nins == 0)
			remove_prehead(fn, blk);
}

/****************************** Главные функции *******************************/

static void readfn (Fn *fn) {
	fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
	fillpreds(fn);
	filluse(fn);
	ssa(fn);
	filluse(fn);

	block_array_t lasts = get_lasts(fn);
	// sort_blocks_array_by_id(lasts);

#ifdef PRINT_LASTS
	printf("lasts:\n");
	print_block_array(lasts);
#endif

	for (int i = 0; i < lasts.size; i++)
		process_as_footer(fn, lasts.blocks[i]);

	free(lasts.blocks);

	remove_empty_preheads(fn);
	// for (Blk *blk = fn->start; blk; blk = blk->link)
	// 	print_block(fn, blk);
	// printf("\n\n");
	printfn(fn, stdout);
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
	parse(stdin, "<stdin>", readdat, readfn);
	freeall();
}
