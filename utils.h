/*==========================================================*/
/*							UTILS							*/
/*==========================================================*/
#pragma once
#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef _WIN32
# ifndef WIN32_LEAN_AND_MEAN
#  define WIN32_LEAN_AND_MEAN
# endif
# include <windows.h>
# undef WIN32_LEAN_AND_MEAN
# define ALIGNED(decl, amt) __declspec(align(amt)) decl
#elif defined(_HAVE_POSIX)
# include <stddef.h>
# include <unistd.h>
# define ALIGNED(decl, amt) decl __attribute__((aligned(amt)))
#else
# error Unsupported platform!
#endif

#if defined(_WIN32)
# define COMPILER_MSVC 1
# if defined(_M_X64)
#  define PTR_SIZE 8
# elif defined(_M_IX86)
#  define PTR_SIZE 4
# else
#  define PTR_SIZE 8
# endif
#elif defined(__GNUC__)
# define COMPILER_GCC 1
# if defined(__x86_64__)
#  define PTR_SIZE 8
# elif defined(__i386__)
#  define PTR_SIZE 4
# elif defined(__arm__)
#  if defined(__ARM_ARCH_7__) || defined(__ARM_ARCH_7A__) || defined(__ARM_ARCH_7EM__) || defined(__ARM_ARCH_7R__) || defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7S__)
#   define PTR_SIZE 4
#  elif defined(__ARM_ARCH_6__) || defined(__ARM_ARCH_6J__) || defined(__ARM_ARCH_6K__) || defined(__ARM_ARCH_6T2__) || defined(__ARM_ARCH_6Z__) || defined(__ARM_ARCH_6ZK__)
#   define PTR_SIZE 4
#  else
#   define PTR_SIZE 8
#  endif
# else
#  define PTR_SIZE 8
# endif
#else
# define PTR_SIZE 8
#endif


typedef struct allocator_i allocator_i;
typedef struct allocator_i {
	/** Allocator context */
	void* ctx;

	/**
	 * Generic allocation function of an allocator
	 * allocator is the allocator context
	 * ptr a pointer to resize or free or a NULL for new allocations
	 * prev_size is the size of the memory block ptr is pointing at
	 * new_size is the requested size of the block after the call
	 */
	void* (*alloc)(allocator_i* a, void* ptr, size_t prev_size, size_t new_size, const char* file, uint32_t line);
} allocator_i;

#define tcmalloc(_a, _s) (_a)->alloc(_a, NULL, 0, _s, __FILE__, __LINE__)
#define tcfree(_a, _p, _s) (_a)->alloc(_a, _p, _s, 0, __FILE__, __LINE__)
#define tcrealloc(_a, _p, _prev, _new) (_a)->alloc(_a, _p, _prev, _new, __FILE__, __LINE__)


/*==========================================================*/
/*					STRETCHY BUFFERS						*/
/*==========================================================*/

/* Vector / Growable / "Stretchy" buffer functions: */

inline void* __buff_growf(void* arr, int increment, int elemsize, allocator_i* a, const char* file, uint32_t line);

#define buff_free(a,alloc)      ((a) ? tc_free(alloc, _buff_raw(a), _buff_m(a) * sizeof(*a) + 2 * sizeof(uint32_t)), 0 : 0)
#define buff_push(a,alloc, ...) (_buff_maygrow(a,1,alloc), (a)[_buff_n(a)++] = (##__VA_ARGS__))
#define buff_pop(a)				((a)[--_buff_n(a)])
#define buff_count(a)			((a) ? _buff_n(a) : 0)
#define buff_add(a,n,alloc)     (_buff_maygrow((a),(n),(alloc)), _buff_n(a)+=(n), &(a)[_buff_n(a)-(n)])
#define buff_last(a)			((a)[_buff_n(a)-1])

#define _buff_raw(a) ((uint32_t*)(void*)(a) - 2)
#define _buff_m(a)   _buff_raw(a)[0]
#define _buff_n(a)   _buff_raw(a)[1]

#define _buff_needgrow(a, n) ((a)==0 || _buff_n(a)+(n) >= _buff_m(a))
#define _buff_maygrow(a, n, alloc)	 (_buff_needgrow(a,(n)) ? _buff_grow(a,n,alloc) : 0)
#define _buff_grow(a, n, alloc)     (*((void**)&(a)) = _buff_growf((a),(n),sizeof(*(a)),(alloc),__FILE__,__LINE__))

/* Vector / Growable buffer functions: */
inline void* __buff_growf(void* arr, int increment, int elemsize, allocator_i* a, const char* file, uint32_t line) {
	uint32_t old_size = arr ? _buff_m(arr) : 0;
	uint32_t new_size = old_size * 2;
	uint32_t min_needed = buff_count(arr) + increment;
	uint32_t size = new_size > min_needed ? new_size : min_needed;
	uint32_t* ptr = (uint32_t*)a->alloc(
		a,
		arr ? _buff_raw(arr) : 0,
		(size_t)old_size * elemsize + (arr ? sizeof(uint32_t) * 2 : 0),
		(size_t)size * elemsize + sizeof(uint32_t) * 2,
		file,
		line
	);
	if (ptr) {
		if (!arr) ptr[1] = 0;
		ptr[0] = size;
		return ptr + 2;
	}
	// Try to force a NULL pointer exception later
	return (void*)(2 * sizeof(uint32_t));
}

/*==========================================================*/
/*							BITARRAY						*/
/*==========================================================*/

#define NUM_BITS (8 * sizeof(uint64_t))
#define INDEX_SHIFT (6ULL)

/** Bit array functions */
static inline void bit_set(uint64_t* arr, uint32_t index) {
	arr[index >> INDEX_SHIFT] |= 1ULL << (index & (NUM_BITS - 1ULL));
}

static inline void bit_clear(uint64_t* arr, uint32_t index) {
	arr[index >> INDEX_SHIFT] &= ~(1ULL << (index & (NUM_BITS - 1ULL)));
}

static inline void bit_toggle(uint64_t* arr, uint32_t index) {
	arr[index >> INDEX_SHIFT] ^= 1ULL << (index & (NUM_BITS - 1ULL));
}

static inline bool bit_test(uint64_t* arr, uint32_t index) {
	return (arr[index >> INDEX_SHIFT] & (1ULL << (index & (NUM_BITS - 1ULL)))) != 0;
}

/*==========================================================*/
/*							LISTS							*/
/*==========================================================*/

/** To loop over all list elements: */
#ifndef list_foreach
#define list_foreach(_list, _node) \
for ((_node) = (_list)->next; (list_t*)(_list) != (list_t*)(_node); (_node) = (_node)->next )
#endif

/** Simple signly linked list */
typedef struct lifo_s {
	struct lifo_s* next;
} lifo_t;

/** Signly linked list with cached pointer to tail node */
typedef struct slist_s {
	lifo_t;
	lifo_t* tail;
} slist_t;

/** Simple doubly linked list */
typedef struct listnode_s {
	struct listnode_s* next;
	struct listnode_s* prev;
} list_t;

static inline void lifo_init(lifo_t* list) { list->next = NULL; }

static inline bool lifo_empty(lifo_t* list) { return list->next == NULL; }

static inline void lifo_push(lifo_t* list, lifo_t* node) {
	node->next = list->next;
	list->next = node;
}

static inline lifo_t* lifo_pop(lifo_t* list) {
	lifo_t* first = list->next;
	if (first) list->next = first->next;
	return first;
}

static inline void slist_init(slist_t* list) { list->next = NULL; list->tail = list; }

static inline bool slist_empty(slist_t* list) { return list->next == NULL; }

static inline void slist_push_front(slist_t* list, lifo_t* node) {
	if (lifo_empty(list)) list->tail = node;
	lifo_push(list, node);
}

static inline lifo_t* slist_pop_front(slist_t* list) {
	lifo_t* node = lifo_pop(list);
	if (lifo_empty(list)) list->tail = list;
	return node;
}

static inline void slist_add_tail(slist_t* list, lifo_t* node) {
	assert(node->next == NULL);
	list->tail->next = node;
	list->tail = node;
}

static inline void list_init(list_t* list) { list->prev = list; list->next = list; }

static inline bool list_empty(list_t* list) { return list->next == list && list->prev == list; }

static inline void list_add(list_t* list, list_t* node) {
	node->prev = list;
	node->next = list->next;
	list->next->prev = node;
	list->next = node;
}

static inline void list_add_tail(list_t* list, list_t* node) {
	node->next = list;
	node->prev = list->prev;
	list->prev->next = node;
	list->prev = node;
}

static inline void list_remove(list_t* node) {
	node->next->prev = node->prev;
	node->prev->next = node->next;
}

static inline list_t* list_first(list_t* list) { return list->next; }

static inline list_t* list_last(list_t* list) { return list->prev; }

static inline list_t* list_pop(list_t* list) {
	list_t* first = NULL;
	if (!list_empty(list)) {
		first = list->next;
		list_remove(first);
	}
	return first;
}

/*==========================================================*/
/*							RB-TREE							*/
/*==========================================================*/

typedef struct rbnode_s {
	size_t data;
	/**
	 * Left and right children and parent pointer,
	 * parent pointer contains a tagged color bit so it cannot be at
	 * odd adresses
	 */
	struct rbnode_s* left, *right, *parent;
} rbnode_t;

typedef struct {
	rbnode_t* root;
	size_t size;
} rbtree_t;

static rbnode_t RBNIL = {
	.data = 0U,
	.left = &RBNIL,
	.right = &RBNIL,
	.parent = &RBNIL,
};

static inline void rb_rotate_left(rbnode_t** root, rbnode_t* x);
static inline void rb_rotate_right(rbnode_t** root, rbnode_t* y);
static inline void rb_insert_fixup(rbnode_t** root, rbnode_t* z);
static inline void rb_delete_fixup(rbnode_t** r, rbnode_t* x);
static inline void rb_transplant(rbnode_t** root, rbnode_t* x, rbnode_t* y);

#define RB_NODE(_x) ((rbnode_t*)((size_t)_x & ~1))
#define RB_COLORBIT(_x) ((size_t) (_x)->parent & 1)
#define RB_RED 1U
#define RB_BLACK 0U
#define RB_SETRED(_x) (_x)->parent = (rbnode_t*)((size_t)(_x)->parent | RB_RED)
#define RB_SETBLACK(_x) (_x)->parent = RB_NODE((_x)->parent)
#define RB_SETCOLOR(_x, _y, _z) (_x)->parent = (rbnode_t*)((size_t)(_y) | (_z));


static inline rbtree_t rb_init() { return (rbtree_t) { .root = &RBNIL }; }

static inline bool rb_empty(rbtree_t* t) { return t->root == &RBNIL; }

static inline rbnode_t* rb_min(rbnode_t* x) {
	for (; x->left != &RBNIL; x = x->left);
	return x;
}

static inline rbnode_t* rb_max(rbnode_t* x) {
	for (; x->right != &RBNIL; x = x->right);
	return x;
}

static inline void rb_insert(rbtree_t* t, rbnode_t* z) {
	assert(RB_NODE(z) == z, "[RB-Tree]: Make sure the new node is on an even address");
	rbnode_t* y = &RBNIL;
	rbnode_t* x = t->root;
	while (x != &RBNIL) {
		y = x;
		if (z->data < x->data)
			x = x->left;
		else x = x->right;
	}
	z->left = z->right = &RBNIL;
	RB_SETCOLOR(z, y, 1U);
	if (y == &RBNIL)
		t->root = z;
	else if (z->data < y->data)
		y->left = z;
	else y->right = z;
	rb_insert_fixup(&t->root, z);
	t->size++;
}

static inline void rb_remove(rbtree_t* t, rbnode_t* z) {
	rbnode_t* y, * x;
	y = z;
	size_t c = RB_COLORBIT(y);
	if (z->left == &RBNIL) {
		x = z->right;
		rb_transplant(&t->root, z, z->right);
	}
	else if (z->right == &RBNIL) {
		x = z->left;
		rb_transplant(&t->root, z, z->left);
	}
	else {
		y = rb_min(z->right);
		c = RB_COLORBIT(y);
		x = y->right;
		if (RB_NODE(y->parent) == z) {
			RB_SETCOLOR(x, y, RB_COLORBIT(x));
		}
		else {
			rb_transplant(&t->root, y, y->right);
			y->right = z->right;
			RB_SETCOLOR(y->right, y, RB_COLORBIT(y->right));
		}
		rb_transplant(&t->root, z, y);
		y->left = z->left;
		RB_SETCOLOR(y->left, y, RB_COLORBIT(y->left));
		RB_SETCOLOR(y, RB_NODE(y->parent), RB_COLORBIT(z));
	}
	if (c == RB_BLACK) rb_delete_fixup(&t->root, x);
	t->size--;
}

static inline rbnode_t* rb_find(rbtree_t* t, size_t key) {
	rbnode_t* x = t->root;
	while (x != &RBNIL) {
		if (x->data == key) return x;
		else if (x->data > key) x = x->left;
		else x = x->right;
	}
	return NULL;
}

static inline rbnode_t* rb_begin(rbtree_t* t) {
	rbnode_t* it = NULL;
	rbnode_t* x = t->root;
	while (x->left != &RBNIL || x->right != &RBNIL) {
		while (x->left != &RBNIL) x = x->left;
		if (x->right != &RBNIL) x = x->right;
	}
	it = x;
	return it;
}

static inline rbnode_t* rb_end(rbtree_t* t) { return &RBNIL; }

static inline size_t rb_size(rbtree_t* t) { return t->size; }

static inline rbnode_t* rb_next(rbnode_t** it) {
	rbnode_t* x = (*it);
	if ((*it)->right != &RBNIL) {
		(*it) = (*it)->right;
		while ((*it)->left != &RBNIL)
			(*it) = (*it)->left;
		return x;
	}
	rbnode_t* p;
	for (;;) {
		p = (*it);
		(*it) = RB_NODE((*it)->parent);
		if ((*it) == &RBNIL) break;
		else if ((*it)->left == p) break;
	}
	return x;
}

static inline rbnode_t* rb_prev(rbnode_t** it) {
	rbnode_t* x = (*it);
	if ((*it)->left != &RBNIL) {
		(*it) = (*it)->left;
		while ((*it)->right != &RBNIL)
			(*it) = (*it)->right;
		return x;
	}
	rbnode_t* p;
	for (;;) {
		p = (*it);
		(*it) = RB_NODE((*it)->parent);
		if ((*it) == &RBNIL) break;
		if ((*it)->right == p) break;
	}
	return x;
}

static inline rbnode_t* rb_lower_bound(rbtree_t* t, size_t key) {
	rbnode_t* x = t->root, * p = &RBNIL;
	rbnode_t* it = p;
	for (;;) {
		if (x == &RBNIL) {
			it = p;
			if (!(p == &RBNIL || key <= p->data))
				rb_next(&it);
			return it;
		}
		p = x;
		if (key > x->data) x = x->right;
		else x = x->left;
	}
	return it;
}

static inline rbnode_t* rb_upper_bound(rbtree_t* t, size_t key) {
	rbnode_t* it = rb_lower_bound(t, key);
	while (it != &RBNIL && it->data == key) rb_next(&it);
	return it;
}

static inline void rb_rotate_left(rbnode_t** root, rbnode_t* x) {
	rbnode_t* y = x->right;
	x->right = y->left;
	if (y->left != &RBNIL)
		RB_SETCOLOR(y->left, x, RB_COLORBIT(y->left));
	RB_SETCOLOR(y, RB_NODE(x->parent), RB_COLORBIT(y));
	if (RB_NODE(x->parent) == &RBNIL) (*root) = y;
	else if (x == RB_NODE(x->parent)->left)
		RB_NODE(x->parent)->left = y;
	else RB_NODE(x->parent)->right = y;
	y->left = x;
	RB_SETCOLOR(x, y, RB_COLORBIT(x));
}

static inline void rb_rotate_right(rbnode_t** root, rbnode_t* y) {
	rbnode_t* x = y->left;
	y->left = x->right;
	if (x->right != &RBNIL)
		RB_SETCOLOR(x->right, y, RB_COLORBIT(x->right));
	RB_SETCOLOR(x, RB_NODE(y->parent), RB_COLORBIT(x));
	if (RB_NODE(x->parent) == &RBNIL) (*root) = x;
	else if (y == RB_NODE(y->parent)->right)
		RB_NODE(y->parent)->right = x;
	else RB_NODE(y->parent)->left = x;
	x->right = y;
	RB_SETCOLOR(y, x, RB_COLORBIT(y));
}

static inline void rb_insert_fixup(rbnode_t** root, rbnode_t* z) {
	rbnode_t* y;
	rbnode_t* p = RB_NODE(z->parent);
	while (z != (*root) && RB_COLORBIT(p) == RB_RED) {
		p = RB_NODE(z->parent);
		if (p == RB_NODE(p->parent)->left) {
			y = RB_NODE(p->parent)->right;
			if (RB_COLORBIT(y) == RB_RED) {
				RB_SETBLACK(p);
				RB_SETBLACK(y);
				p = RB_NODE(p->parent);
				RB_SETRED(p);
				z = p;
			}
			else {
				if (z == p->right) {
					z = p;
					rb_rotate_left(root, z);
				}
				p = RB_NODE(z->parent);
				RB_SETBLACK(p);
				p = RB_NODE(p->parent);
				RB_SETRED(p);
				rb_rotate_right(root, p);
			}
		}
		else {
			y = RB_NODE(RB_NODE(z->parent)->parent)->left;
			if (RB_COLORBIT(y) == RB_RED) {
				RB_SETBLACK(p);
				RB_SETBLACK(y);
				p = RB_NODE(p->parent);
				RB_SETRED(p);
				z = p;
			}
			else {
				if (z == p->left) {
					z = p;
					rb_rotate_right(root, z);
				}
				p = RB_NODE(z->parent);
				RB_SETBLACK(p);
				p = RB_NODE(p->parent);
				RB_SETRED(p);
				rb_rotate_left(root, p);
			}
		}
		p = RB_NODE(z->parent);
	}
	RB_SETBLACK(*root);
}

static inline void rb_delete_fixup(rbnode_t** r, rbnode_t* x) {
	while (x != *r && RB_COLORBIT(RB_NODE(x->parent)) == 0) {
		rbnode_t* y, * p;
		if (x == RB_NODE(x->parent)->left) {
			y = RB_NODE(x->parent)->right;
			if (RB_COLORBIT(y)) {
				RB_SETBLACK(y);
				p = RB_NODE(x->parent);
				RB_SETRED(p);
				rb_rotate_left(r, p);
				y = RB_NODE(x->parent)->right;
			}
			if (RB_COLORBIT(y->left) == RB_BLACK &&
				RB_COLORBIT(y->right) == RB_BLACK) {
				RB_SETRED(y);
				x = RB_NODE(x->parent);
			}
			else {
				if (RB_COLORBIT(y->right) == RB_BLACK) {
					RB_SETBLACK(y->left);
					RB_SETRED(y->parent);
					rb_rotate_right(r, y);
					y = RB_NODE(y->parent)->right;
				}
				RB_SETCOLOR(y, RB_NODE(y->parent), RB_COLORBIT(RB_NODE(x->parent)));
				p = RB_NODE(x->parent);
				RB_SETBLACK(p);
				RB_SETBLACK(y->right);
				rb_rotate_left(r, RB_NODE(x->parent));
				x = (*r);
			}
		}
		else {
			y = RB_NODE(x->parent)->left;
			if (RB_COLORBIT(y)) {
				RB_SETBLACK(y);
				p = RB_NODE(x->parent);
				RB_SETRED(p);
				rb_rotate_right(r, p);
				y = p->left;
			}
			if (RB_COLORBIT(y->right) == RB_BLACK &&
				RB_COLORBIT(y->left) == RB_BLACK) {
				RB_SETRED(y);
				x = RB_NODE(x->parent);
			}
			else {
				if (RB_COLORBIT(y->left) == RB_BLACK) {
					RB_SETBLACK(y->right);
					RB_SETRED(y);
					rb_rotate_left(r, y);
					y = RB_NODE(y->parent)->left;
				}
				RB_SETCOLOR(y, RB_NODE(y->parent), RB_COLORBIT(RB_NODE(x->parent)));
				p = x->parent;
				RB_SETBLACK(p);
				RB_SETBLACK(y->left);
				rb_rotate_right(r, RB_NODE(x->parent));
				x = (*r);
			}
		}
	}
	RB_SETBLACK(x);
}

static inline void rb_transplant(rbnode_t** root, rbnode_t* x, rbnode_t* y) {
	if (RB_NODE(x->parent) == &RBNIL) (*root) = y;
	else if (x == RB_NODE(x->parent)->left)
		RB_NODE(x->parent)->left = y;
	else RB_NODE(x->parent)->right = y;
	RB_SETCOLOR(y, RB_NODE(x->parent), RB_COLORBIT(y));
}

/*==========================================================*/
/*					REGION ALLOCATOR		    			*/
/*==========================================================*/

#define TEMP_INIT(a) temp_t a; temp_init((&a), NULL)

#define TEMP_CLOSE(a) temp_free((&a))

// Smallest possible slab size
#define SLAB_MIN_SIZE (((size_t)USHRT_MAX) + 1)
#define CHUNK_SIZE (4096)


typedef struct temp_s {
	allocator_i;

	char buffer[1024];

	allocator_i* parent;

	void* next;
} temp_t;

static inline void temp_init(temp_t* a, allocator_i* parent);

static inline void* temp_realloc(temp_t* a, void* ptr, size_t old_size, size_t new_size, const char* file, uint32_t line);

static inline void temp_free(temp_t* a);

typedef struct temp_internal_s {
	uint64_t used;
	uint64_t cap;
	uint8_t* end;
} temp_internal_t;

typedef struct temp_node_s {
	uint64_t size;
	void* next;
} temp_node_t;


void temp_init(temp_t* a, allocator_i* parent) {
	a->ctx = a;
	a->alloc = temp_realloc;
	a->parent = parent;
	temp_internal_t* temp = (temp_internal_t*)a->buffer;
	temp->used = sizeof(temp_internal_t);
	temp->cap = sizeof(a->buffer);
	temp->end = (temp + 1);
	a->next = NULL;
}

void* temp_realloc(temp_t* a, void* ptr, size_t old_size, size_t new_size, const char* file, uint32_t line) {
	temp_internal_t* temp = (temp_internal_t*)a->buffer;
	if (new_size > old_size) {
		if (temp->used + new_size > temp->cap) {
			size_t size = min(CHUNK_SIZE, next_power_of_2(new_size + sizeof(temp_node_t)));
			temp_node_t* node = tcmalloc(a->parent, size);
			node->size = size;
			node->next = a->next;
			a->next = node;
			temp->used = sizeof(temp_node_t);
			temp->cap = size;
			temp->end = (node + 1);
		}
		ptr = temp->end;
		temp->used += new_size;
		temp->end += new_size;
	}
	return ptr;
}

void temp_free(temp_t* a) {
	temp_node_t* node = a->next;
	while (node) {
		temp_node_t* ptr = node;
		node = node->next;
		tc_free(a->parent, ptr, ptr->size);
	}
}

/*==========================================================*/
/*						ATOMIC TYPES						*/
/*==========================================================*/
#if defined(_WIN32)
#include <intrin.h>

typedef struct { size_t _nonatomic; } atomic_t;

#define thread_fence_acquire() _ReadWriteBarrier()
#define thread_fence_release() _ReadWriteBarrier()
#else
typedef struct { void* volatile _nonatomic; } __attribute__((aligned(PTR_SIZE))) atomic_t;

#define thread_fence_acquire() asm volatile("" ::: "memory")
#define thread_fence_release() asm volatile("" ::: "memory")
#endif

static inline size_t atomic_load(const atomic_t* object, bool acquire) {
	size_t result = object->_nonatomic;
	if (acquire) thread_fence_acquire();
	return result;
}

static inline void atomic_store(atomic_t* object, size_t desired, bool release) {
	if (release) thread_fence_release();
	object->_nonatomic = desired;
}

static inline bool compare_exchange_weak(atomic_t* object, size_t* expected, size_t desired) {
#if defined(_WIN32)
# if PTR_SIZE == 8
	uint64_t e = *expected;
	uint64_t previous = _InterlockedCompareExchange64((LONGLONG*)object, desired, e);
# elif PTR_SIZE == 4
	uint32_t e = *expected;
	uint32_t previous = _InterlockedCompareExchange((long*)object, desired, e);
# endif
#else
# if PTR_SIZE == 8
	uint64_t e = *expected;
	uint64_t previous;
	asm volatile("lock; cmpxchgq %2, %1" : "=a"(previous), "+m"(object->_nonatomic) : "q"(desired), "0"(e));
# elif PTR_SIZE == 4
	int32_t e = *expected;
	uint32_t previous;
	asm volatile("lock; cmpxchgl %2, %1" : "=a"(previous), "+m"(object->_nonatomic) : "q"(desired), "0"(e));
# endif
#endif
	intptr_t matched = (previous == e);
	if (!matched) *expected = previous;
	return matched;
}

static inline bool compare_exchange_strong(atomic_t* object, size_t* expected, size_t desired) {
	thread_fence_release();
	size_t prev;
#if defined(_WIN32)
# if PTR_SIZE == 8
	prev = _InterlockedCompareExchange64((LONGLONG*)object, desired, expected);
# elif PTR_SIZE == 4
	prev = _InterlockedCompareExchange((long*)object, desired, expected);
# endif
#else
# if PTR_SIZE == 8
	asm volatile("lock; cmpxchgq %2, %1" : "=a"(prev), "+m"(object->_nonatomic) : "q"(desired), "0"(expected));
# elif PTR_SIZE == 4
	asm volatile("lock; cmpxchgl %2, %1" : "=a"(prev), "+m"(object->_nonatomic) : "q"(desired), "0"(expected));
# endif
#endif
	thread_fence_acquire();
	bool result = (prev == *expected);
	if (!result) *expected = prev;
	return result;
}

#define CAS(_x, _y, _z) compare_exchange_strong((atomic_t*)(_x), (size_t*)&(_y), (size_t)(_z))

/*==========================================================*/
/*					LOCK-FREE PAGE LIFO/STACK				*/
/*==========================================================*/

/* Can only be used to store 64k aligned pointers since it uses the lower 16 bits as counter/tag to track reuse in the ABA problem */

typedef struct lf_lifo_t {
	void* next;
} lf_lifo_t;

static inline intptr_t aba_value(void* a) {
	return (intptr_t)a & 0xffff;
}

static inline lf_lifo_t* lf_lifo(void* a) {
	return (lf_lifo_t*)((intptr_t)a & ~0xffff);
}

static inline void lf_lifo_init(lf_lifo_t* head) {
	head->next = NULL;
}

static inline bool lf_lifo_is_empty(lf_lifo_t* head) {
	return lf_lifo(head->next) == NULL;
}

static inline lf_lifo_t* lf_lifo_push(lf_lifo_t* head, void* elem) {
	assert(lf_lifo(elem) == elem); // Should be aligned address
	do {
		void* tail = head->next;
		lf_lifo(elem)->next = tail;
		void* newhead = (char*)elem + aba_value((char*)tail + 1);
		if (CAS(&head->next, tail, newhead))
			return head;
	} while (true);
}

static inline void* lf_lifo_pop(lf_lifo_t* head) {
	do {
		void* tail = head->next;
		lf_lifo_t* elem = lf_lifo(tail);
		if (elem == NULL) return NULL;
		void* newhead = ((char*)lf_lifo(elem->next) + aba_value(tail));
		if (CAS(&head->next, tail, newhead)) return elem;
	} while (true);
}

/*==========================================================*/
/*						LOCK-FREE QUEUE						*/
/*==========================================================*/

/* This is a fixed-size (FIFO) ring buffer that allows for multiple concurrent reads and writes */

typedef struct cell_s cell_t;

typedef struct lf_queue_s {
	allocator_i* base;
	size_t mask;
	ALIGNED(cell_t*, 64) buffer;
	ALIGNED(atomic_t, 64) write;
	ALIGNED(atomic_t, 64) read;
} lf_queue_t;

typedef struct cell_s {
	atomic_t sequence;
	void* data;
} cell_t;

static inline lf_queue_t* lf_queue_init(uint32_t elements, allocator_i* a) {
	lf_queue_t* queue = (lf_queue_t*)tcmalloc(a, sizeof(lf_queue_t) + elements * sizeof(cell_t));
	queue->base = a;
	queue->buffer = (cell_t*)(queue + 1);
	queue->mask = elements - 1;
	assert((elements >= 2) && ((elements & (elements - 1)) == 0));
	for (size_t i = 0; i != elements; i++)
		atomic_store(&queue->buffer[i].sequence, i, false);
	atomic_store(&queue->write, 0, false);
	atomic_store(&queue->read, 0, false);
	return queue;
}

static inline bool lf_queue_put(lf_queue_t* queue, void* data) {
	cell_t* cell;
	size_t pos = (size_t)atomic_load(&queue->write, false);
	for (;;) {
		cell = &queue->buffer[pos & queue->mask];
		size_t seq = (size_t)atomic_load(&cell->sequence, true);
		intptr_t dif = (intptr_t)seq - (intptr_t)pos;
		if (dif == 0) {
			if (compare_exchange_weak(&queue->write, &pos, pos + 1)) break;
		}
		else if (dif < 0) return false;
		else pos = (size_t)atomic_load(&queue->write, false);
	}
	cell->data = data;
	atomic_store(&cell->sequence, pos + 1, true);
	return true;
}

static inline bool lf_queue_get(lf_queue_t* queue, void** data) {
	cell_t* cell;
	size_t pos = atomic_load(&queue->read, false);
	for (;;) {
		cell = &queue->buffer[pos & queue->mask];
		size_t seq = (size_t)atomic_load(&cell->sequence, true);
		intptr_t dif = (intptr_t)seq - (intptr_t)(pos + 1);
		if (dif == 0) {
			if (compare_exchange_weak(&queue->read, &pos, pos + 1)) break;
		}
		else if (dif < 0) return false;
		else pos = (size_t)atomic_load(&queue->read, false);
	}
	*data = cell->data;
	atomic_store(&cell->sequence, pos + queue->mask + 1, true);
	return true;
}

static inline void lf_queue_destroy(lf_queue_t* queue) {
	tcfree(queue->base, queue, sizeof(lf_queue_t) + ((queue->mask + 1) * sizeof(cell_t)), 0);
}

/*==========================================================*/
/*				LOCK-FREE REGION ALLOCATOR					*/
/*==========================================================*/

typedef struct region_s {
	allocator_i base;
	lf_lifo_t slabs;
	allocator_i* parent;
} region_t;

/** Header struct for each region block */
struct rslab {
	lf_lifo_t next;
	size_t size;
	uintptr_t head;
};

static inline uintptr_t _align_ptr(uintptr_t* ptr, uintptr_t align);

static void* region_alloc(allocator_i* a, void* ptr, size_t old_size, size_t new_size, const char* file, uint32_t line);

/** Region allocator functions: */

allocator_i* region_create(allocator_i* base) {
	region_t* region = tc_malloc(base, sizeof(region_t));
	region->parent = base;
	region->slabs.next = 0;
	region->base.ctx = region;
	region->base.alloc = region_alloc;
	return &region->base;
}

void* region_aligned_alloc(region_t* region, size_t size, size_t align) {
	struct rslab* r = lf_lifo(region->slabs.next);
	if (lf_lifo_is_empty(&region->slabs) || (_align_ptr(r->head, align) + size - (size_t)r < r->size)) {
		// If no region exists or region is too full allocate new slab
		size_t slab_size = max(next_power_of_2(size + sizeof(struct rslab)), SLAB_MIN_SIZE);
		r = tc_malloc(region->parent, slab_size);
		r->size = slab_size;
		r->head = (size_t)r + sizeof(struct rslab);
		lf_lifo_push(&region->slabs, r);
	}
	size_t ptr = _align_ptr(r->head, align);
	r->head = ptr + size;
	return ptr;
}

static
void* region_alloc(allocator_i* a, void* ptr, size_t old_size, size_t new_size, const char* file, uint32_t line) {
	region_t* region = a->ctx;
	if (!ptr && new_size > 0) return region_aligned_alloc(region, new_size, 4);
	else TC_ASSERT(old_size == 0, "[Memory]: Freeing from region allocator is not implemented");
	return NULL;
}

void region_destroy(allocator_i* a) {
	region_t* region = a->ctx;
	for (;;) {
		struct rslab* r = lf_lifo_pop(&region->slabs);
		if (r) tc_free(region->parent, r, r->size);
		else return;
	}
}

// Align upwards, align should be power of 2
static inline uintptr_t _align_ptr(uintptr_t* ptr, uintptr_t align) {
	if (align == 0) return ptr;
	// Must be power of 2
	TC_ASSERT(align > 0 && (align & (align - 1)) == 0);
	TC_ASSERT(ptr != NULL);
	// Round up to align-byte boundary
	uintptr_t addr = (uintptr_t)ptr;
	addr = (addr + (align - 1)) & -align;
	TC_ASSERT(addr >= (uintptr_t)ptr);
	return addr;
}

/*==========================================================*/
/*						HASH FUNCTIONS						*/
/*==========================================================*/

// Code based on MurmurHash2, 64-bit versions, by Austin Appleby
//
// All code is released to the public domain. For business purposes, Murmurhash is
// under the MIT license.

static inline uint64_t hash64(const void* key, uint32_t len, uint64_t seed) {
	const uint64_t m = 0xc6a4a7935bd1e995ULL;
	const int r = 47;

	uint64_t h = seed ^ (len * m);

	const uint64_t* data = (const uint64_t*)key;
	const uint64_t* end = data + (len / 8);

	while (data != end) {
		uint64_t k = *data++;

		k *= m;
		k ^= k >> r;
		k *= m;

		h ^= k;
		h *= m;
	}

	const unsigned char* data2 = (const unsigned char*)data;

	switch (len & 7) {
	case 7:
		h ^= (uint64_t)(data2[6]) << 48;
	case 6:
		h ^= (uint64_t)(data2[5]) << 40;
	case 5:
		h ^= (uint64_t)(data2[4]) << 32;
	case 4:
		h ^= (uint64_t)(data2[3]) << 24;
	case 3:
		h ^= (uint64_t)(data2[2]) << 16;
	case 2:
		h ^= (uint64_t)(data2[1]) << 8;
	case 1:
		h ^= (uint64_t)(data2[0]);
		h *= m;
	};

	h ^= h >> r;
	h *= m;
	h ^= h >> r;

	return h;
}

static inline uint64_t hash_str(const char* s) {
	return s ? hash64(s, (uint32_t)strlen(s), 0) : 0;
}

static inline uint64_t hash_str_len(const char* s, uint32_t len) {
	return s ? hash64(s, len, 0) : 0;
}

/** Definition of hashmap functions */

// Large value integer hashmap (for pointers and such)
typedef struct {
	uint64_t* keys;
	uint64_t* vals;
	uint32_t cap;
	allocator_i* a;
} hash_t;

#define MAX_CHAIN_LENGTH 8
#define INITIAL_MAP_SIZE 4

/** Private function definitions: */
static inline int32_t hash_hash(hash_t* m, uint64_t key);
static inline bool hash_rehash(hash_t* map);

/* Definition of hashmap functions */

/** Initialize a new hashmap with 64 bit keys and values */
inline void hash_init(hash_t* map, allocator_i* a) {
	map->cap = INITIAL_MAP_SIZE;
	map->a = a;
	size_t s = map->cap * sizeof(uint64_t);
	map->keys = tcmalloc(a, s * 2);
	memset(map->keys, 0, s * 2);
	map->vals = (size_t)map->keys + s;
}

/** Put 64 bit value value in the hashmap at 64 bit key */
inline bool hash_put(hash_t* map, uint64_t key, uint64_t value) {
	assert(key != 0);
	int32_t i = hash_hash(map, key);
	while (i < 0) {
		if (!hash_rehash(map)) return false;
		i = hash_hash(map, key);
	}
	map->keys[i] = key;
	map->vals[i] = value;
	return true;
}

/** Returns value at key or returns 0 */
inline uint64_t hash_get(hash_t* map, uint64_t key) {
	assert(key != 0);
	if (map->keys == NULL) return 0;
	uint64_t curr = key & (map->cap - 1);
	for (uint32_t i = 0; i < MAX_CHAIN_LENGTH; i++) {
		if (map->keys[curr] == key) return map->vals[curr];
		curr = (curr + 1) & (map->cap - 1);
	}
	return 0;
}

/** Remove value at key from the hashmap */
inline bool hash_remove(hash_t* map, uint64_t key) {
	assert(key != 0);
	if (map->keys == NULL) return false;
	uint64_t curr = key & (map->cap - 1);
	for (uint32_t i = 0; i < MAX_CHAIN_LENGTH; i++) {
		if (map->keys[curr] == key) {
			map->keys[curr] = 0;
			map->vals[curr] = 0;
			return true;
		}
		curr = (curr + 1) & (map->cap - 1);
	}
	return false;
}

/** Free memory allocated by the hashmap */
inline void hash_free(hash_t* map) {
	tcfree(map->a, map->keys, (size_t)map->cap * 2 * sizeof(uint64_t), 0);
}

static inline int32_t hash_hash(hash_t* m, uint64_t key) {
	uint32_t curr = key & (m->cap - 1);
	for (uint32_t i = 0; i < MAX_CHAIN_LENGTH; i++) {
		if (m->keys[curr] == 0 || m->keys[curr] == key) {
			return curr;
		}
		curr = (curr + 1) & (m->cap - 1);
	}
	return -1;
}

static inline bool hash_rehash(hash_t* map) {
	size_t size = map->cap;
	size_t new_size = 2 * size;
	uint64_t* temp_keys = tcmalloc(map->a, new_size * 2 * sizeof(uint64_t));
	memset(temp_keys, 0, new_size * 2 * sizeof(uint64_t));
	uint64_t* temp_vals = ((size_t)temp_keys) + new_size * sizeof(uint64_t);
	uint64_t* curr_keys = map->keys; map->keys = temp_keys;
	uint64_t* curr_vals = map->vals; map->vals = temp_vals;
	map->cap = new_size;
	for (size_t i = 0; i < size; i++) {
		if (curr_keys[i] == 0) continue;
		if (!hash_put(map, curr_keys[i], curr_vals[i])) return false;
	}
	tcfree(map->a, curr_keys, size * 2 * sizeof(uint64_t));
	return true;
}

/*==========================================================*/
/*							STRINGS							*/
/*==========================================================*/

typedef struct stringentry_s stringentry_t;

typedef struct strings_s {
	allocator_i* base;
	stringentry_t* entries; /* buff */
	uint32_t free_entry;
	hash_t lookup;
} strings_t;

/** Private structs */

typedef struct stringentry_s {
	char* string;
	uint64_t hash;
	int16_t len;
	int16_t ref;
} stringentry_t;

/** Create a new string pool */
inline void str_init(strings_t* pool, allocator_i* a) {
	pool->base = a;
	hash_init(&pool->lookup, pool->base);
}

inline void str_free(strings_t* pool) {
	uint32_t entries = buff_count(pool->entries);
	for (uint32_t i = 0; i < entries; i++) {
		stringentry_t entry = pool->entries[i];
		if (entry.ref)
			tcfree(pool->base, entry.string - sizeof(uint32_t), entry.len + 1 + sizeof(uint32_t));
	}
	buff_free(pool->entries, pool->base);
	hash_free(&pool->lookup);
}

#define PAGEBITS 12
#define PAGESIZE (1<<PAGEBITS)

/**
 * Looks up a string and returns the existing handle or returns a new handle and stores the string internally.
 * Reference count gets increased.
 */
inline uint64_t str_intern(strings_t* pool, const char* str, uint32_t len) {
	if (!len) return 0;
	assert(len < PAGESIZE);
	uint64_t hash = tc_hash_str_len(str, len);
	uint32_t index = hash_get(&pool->lookup, hash);
	if (index) {
		stringentry_t* entry = &pool->entries[index - 1];
		assert(entry->hash == hash,
			"[String]: Corrupted hash in entry");
		assert(entry->len == len && memcmp(entry->string, str, len) == 0, \
			"[String]: Hash collision detected between %s and %s. You should change the string or hash function", entry->string, str);
		// Increase reference count
		entry->ref++;
	}
	else {
		// String not found, put it it in the pool
		size_t data_size = len + 1 + sizeof(uint32_t);
		char* data = tc_malloc(pool->base, data_size);
		stringentry_t new_entry = { .string = data + sizeof(uint32_t), .hash = hash, .len = len, .ref = 1 };
		if (pool->free_entry) {
			index = pool->free_entry;
			pool->free_entry = *(uint32_t*)&pool->entries[index - 1];
			pool->entries[index - 1] = new_entry;
		}
		else {
			// Add 1 so we can check for zero index
			index = buff_count(pool->entries) + 1;
			buff_push(pool->entries, pool->base, new_entry);
		}
		hash_put(&pool->lookup, hash, index);
		// Copy string to storage
		*(uint32_t*)data = len;
		data += sizeof(uint32_t);
		memcpy(data, str, len);
		data[len] = '\0';
	}
	return hash;
}

/**
 * Increase reference to a string, make sure to release the reference at cleanup
 */
inline uint64_t str_retain(strings_t* pool, uint64_t sid) {
	if (sid) {
		uint32_t index = hash_get(&pool->lookup, sid);
		assert(index);
		stringentry_t* entry = &pool->entries[index - 1];
		++entry->ref;
	}
	return sid;
}

/**
 * Drops reference to a string. When no references exist the string gets garbage collected.
 */
inline void str_release(strings_t* pool, uint64_t sid) {
	if (sid) {
		uint32_t index = hash_get(&pool->lookup, sid);
		assert(index);
		stringentry_t* entry = &pool->entries[index - 1];
		if (--entry->ref == 0) {
			// Free entry and string
			hash_remove(&pool->lookup, entry->hash);
			tcfree(pool->base, entry->string - sizeof(uint32_t), entry->len + 1 + sizeof(uint32_t));
			memset(entry, 0, sizeof(stringentry_t));
			// Add entry to free entries list
			*(uint32_t*)entry = pool->free_entry;
			pool->free_entry = index;
		}
	}
}

/**
 * Returns a pointer to internally stored string and optionally its length .
 * (Do not use the pointer after interning another string)
 */
inline const char* str_get(strings_t* pool, uint64_t sid, uint32_t* len) {
	if (sid) {
		uint32_t index = hash_get(&pool->lookup, sid);
		if (index) {
			stringentry_t entry = pool->entries[index - 1];
			if (len) *len = entry.len;
			return entry.string;
		}
	}
	return NULL;
}
