/*
 *  x86 memory access helpers
 *
 *  Copyright (c) 2003 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, see <http://www.gnu.org/licenses/>.
 */

#include "cpu.h"
#include "cpu-all.h"
#include "helper.h"

#if !defined(CONFIG_USER_ONLY)
#include "softmmu_exec.h"
#endif /* !defined(CONFIG_USER_ONLY) */

#define SANITY_CHECKING

#ifdef SANITY_CHECKING
#define SANITY_ASSERT(x) assert(x)
#else
#define SANITY_ASSERT(x)
#endif /* SANITY_CHECKING */

/* broken thread support */

static spinlock_t global_cpu_lock = SPIN_LOCK_UNLOCKED;

void helper_lock(void)
{
    spin_lock(&global_cpu_lock);
}

void helper_unlock(void)
{
    spin_unlock(&global_cpu_lock);
}

void helper_cmpxchg8b(CPUX86State *env, target_ulong a0)
{
    uint64_t d;
    int eflags;

    eflags = cpu_cc_compute_all(env, CC_OP);
    d = cpu_ldq_data(env, a0);
    if (d == (((uint64_t)EDX << 32) | (uint32_t)EAX)) {
        cpu_stq_data(env, a0, ((uint64_t)ECX << 32) | (uint32_t)EBX);
        eflags |= CC_Z;
    } else {
        /* always do the store */
        cpu_stq_data(env, a0, d);
        EDX = (uint32_t)(d >> 32);
        EAX = (uint32_t)d;
        eflags &= ~CC_Z;
    }
    CC_SRC = eflags;
}

#ifdef TARGET_X86_64
void helper_cmpxchg16b(CPUX86State *env, target_ulong a0)
{
    uint64_t d0, d1;
    int eflags;

    if ((a0 & 0xf) != 0) {
        raise_exception(env, EXCP0D_GPF);
    }
    eflags = cpu_cc_compute_all(env, CC_OP);
    d0 = cpu_ldq_data(env, a0);
    d1 = cpu_ldq_data(env, a0 + 8);
    if (d0 == EAX && d1 == EDX) {
        cpu_stq_data(env, a0, EBX);
        cpu_stq_data(env, a0 + 8, ECX);
        eflags |= CC_Z;
    } else {
        /* always do the store */
        cpu_stq_data(env, a0, d0);
        cpu_stq_data(env, a0 + 8, d1);
        EDX = d1;
        EAX = d0;
        eflags &= ~CC_Z;
    }
    CC_SRC = eflags;
}
#endif

void helper_boundw(CPUX86State *env, target_ulong a0, int v)
{
    int low, high;

    low = cpu_ldsw_data(env, a0);
    high = cpu_ldsw_data(env, a0 + 2);
    v = (int16_t)v;
    if (v < low || v > high) {
        raise_exception(env, EXCP05_BOUND);
    }
}

void helper_boundl(CPUX86State *env, target_ulong a0, int v)
{
    int low, high;

    low = cpu_ldl_data(env, a0);
    high = cpu_ldl_data(env, a0 + 4);
    if (v < low || v > high) {
        raise_exception(env, EXCP05_BOUND);
    }
}

#if !defined(CONFIG_USER_ONLY)

#define MMUSUFFIX _mmu

#define SHIFT 0
#include "softmmu_template.h"

#define SHIFT 1
#include "softmmu_template.h"

#define SHIFT 2
#include "softmmu_template.h"

#define SHIFT 3
#include "softmmu_template.h"

#endif

#if !defined(CONFIG_USER_ONLY)
/* try to fill the TLB and return an exception if error. If retaddr is
   NULL, it means that the function was called in C code (i.e. not
   from generated code or from helper.c) */
/* XXX: fix it to restore all registers */
void tlb_fill(CPUX86State *env, target_ulong addr, int is_write, int mmu_idx,
              uintptr_t retaddr)
{
    TranslationBlock *tb;
    int ret;

    ret = cpu_x86_handle_mmu_fault(env, addr, is_write, mmu_idx);
    if (ret) {
        if (retaddr) {
            /* now we have a real cpu fault */
            tb = tb_find_pc(retaddr);
            if (tb) {
                /* the PC is inside the translated code. It means that we have
                   a virtual CPU fault */
                cpu_restore_state(tb, env, retaddr);
            }
        }
        raise_exception_err(env, env->exception_index, env->error_code);
    }
}
#endif

//static inline target_ulong
//do_memory_load(uint8_t *p, int idx, bool sign)
//{
//  switch (idx & 3) {
//  case 0:
//    // ld8
//
//    if (sign)
//      return (target_ulong) ((int8_t)*p);
//    else
//      return (target_ulong) *p;
//
//  case 1:
//    // ld16
//
//    if (sign)
//      return (target_ulong) ((int16_t)tswap16(*((uint16_t *)p)));
//    else
//      return (target_ulong) tswap16(*((uint16_t *)p));
//
//  case 2:
//    // ld32
//
//    if (sign)
//      return (target_ulong) ((int32_t)tswap32(*((uint32_t *)p)));
//    else
//      return (target_ulong) tswap32(*((uint32_t *)p));
//
//  default:
//  case 3:
//#ifdef TARGET_X86_64
//    // ld64
//
//    if (sign)
//      return (target_ulong) ((int64_t)tswap64(*((uint64_t *)p)));
//    else
//      return (target_ulong) tswap64(*((uint64_t *)p));
//
//#else
//    /* Should never happen on 32-bit targets.  */
//    assert(false);
//#endif
//    break;
//  }
//
//  return 0;
//}

static void bad_cache_line_call(CPUX86CacheLine *line)
{
  assert(false);
}

void helper_xbegin(CPUX86State *env, target_ulong abort_addr)
{
  printf("helper_xbegin(): abort=0x%llx\n", (unsigned long long) abort_addr);
  printf("current esp: 0x%llx\n", (unsigned long long) env->regs[R_ESP]);
  printf("current ebp: 0x%llx\n", (unsigned long long) env->regs[R_EBP]);
  if (env->htm_nest_level++ == 0) {
    // begin of HTM region
    printf("htm region begin- checkpointing CPU state\n");
    memcpy((char *) &env->htm_checkpoint_state,
           (const char *) env,
           sizeof(CPUX86StateCheckpoint));
    env->htm_abort_eip = abort_addr;

    // assert no dirty cache lines (since we were previously not in txn)
    cpu_htm_hash_table_iterate(env, bad_cache_line_call);
  }
}

#if defined(CONFIG_USER_ONLY)
static void cache_line_commit(CPUX86CacheLine *line)
{
  uint8_t *p;
  int i;
  p = (uint8_t *)(X86_HTM_CNO_TO_ADDR(line->cno) + GUEST_BASE);
  printf("cache_line_commit: commit CL starting at: 0x%llx\n",
         (unsigned long long) p);
  memmove(p, &line->data[0], X86_CACHE_LINE_SIZE);
  SANITY_ASSERT(memcmp(p, &line->data[0], X86_CACHE_LINE_SIZE) == 0);

  for (i = 0; i < X86_CACHE_LINE_SIZE/8; i++) {
    printf("0x%llx: 0x%llx\n",
           (unsigned long long)(p + i * 8),
           (unsigned long long) *((uint64_t *)(p + i * 8)));
  }
}
#else
static void cache_line_commit(CPUX86CacheLine *line)
{
  // XXX: implement
  assert(false);
}
#endif /* defined(CONFIG_USER_ONLY) */

void helper_xend(CPUX86State *env)
{
  printf("helper_xend()\n");
  // XXX: signal processor exception
  assert(env->htm_nest_level > 0);
  if (--env->htm_nest_level == 0) {
    printf("htm region end\n");

    // commit memory changes
    cpu_htm_hash_table_iterate(env, cache_line_commit);
    cpu_htm_hash_table_reset(env);

    printf("memory changes commited\n");
    assert(env->htm_nest_level == 0);
  }
}

void helper_xabort(CPUX86State *env, int32_t imm8)
{
  printf("helper_xabort(imm8=%d)\n", imm8);
  printf("current esp: 0x%llx\n", (unsigned long long) env->regs[R_ESP]);
  printf("current ebp: 0x%llx\n", (unsigned long long) env->regs[R_EBP]);
  if (env->htm_nest_level == 0)
    // no-op
    return;

  env->htm_nest_level = 0;

  // restore register state
  memcpy((char *) env,
         (const char *) &env->htm_checkpoint_state,
         sizeof(CPUX86StateCheckpoint));

  // restore memory state
  cpu_htm_hash_table_reset(env);

  // set high bits of EAX to imm8
  env->regs[R_EAX] |= imm8 << 24;

  // XXX: what else do we need to do to EAX?

  // go to abort handler
  env->eip = env->htm_abort_eip;
  printf("set env to go to eip=0x%llx\n", (unsigned long long) env->eip);
  printf("restored esp: 0x%llx\n", (unsigned long long) env->regs[R_ESP]);
  printf("restored ebp: 0x%llx\n", (unsigned long long) env->regs[R_EBP]);
}

static inline uint32_t
mem_idx_to_size(uint32_t idx)
{
  switch (idx & 3) {
  case 0: return 1;
  case 1: return 2;
  case 2: return 4;
  default:
  case 3: return 8;
  }
}

#if defined(CONFIG_USER_ONLY)
static inline CPUX86CacheLine*
load_cacheline(CPUX86State *env, target_ulong cno, bool alloc)
{
  bool r;
  CPUX86CacheLine *cline;
  // load the cache line into per-cpu buffer
  if (!(cline = cpu_htm_hash_table_lookup(env, cno)) && alloc) {

    // not found, need to allocate a new cache line
    cline = cpu_htm_get_free_cache_line(env);
    if (!cline)
      // cannot load cachline
      return 0;

    // read the cache line from memory, to fill the buffer
    memmove(&cline->data[0],
        (uint8_t *)X86_HTM_CNO_TO_ADDR(cno) + GUEST_BASE,
        X86_CACHE_LINE_SIZE);

    cline->cno = cno;
    if (!(r = cpu_htm_hash_table_insert(env, cline)))
      assert(false);
    SANITY_ASSERT(cpu_htm_hash_table_lookup(env, cno) == cline);
  }
  SANITY_ASSERT(!cline || cline->cno == cno);
  return cline;
}
#endif /* defined(CONFIG_USER_ONLY) */

#if defined(CONFIG_USER_ONLY)
static inline void
do_split_read(const uint8_t *p0,
              const uint8_t *p1,
              uint8_t *buf,
              uint32_t split,
              uint32_t size)
{
  memmove(buf, p0, split);
  if (size > split)
    memmove(buf + split, p1, size - split);
}

static inline target_ulong helper_htm_mem_load_helper(
    CPUX86State *env, target_ulong a0, uint32_t idx, bool sign)
{

  // XXX: should be static_assert
  SANITY_ASSERT(sizeof(target_ulong) <= X86_CACHE_LINE_SIZE);

  target_ulong cno0, cno1; /* need at most two cache lines */
  CPUX86CacheLine *cline0, *cline1;

  uint8_t *p0, *p1, buf[sizeof(target_ulong)];
  uint32_t split, size;

  size = mem_idx_to_size(idx);
  split = size;

  if (X86_HTM_IN_TXN(env)) {

    // convert a0 to cache line number(s)
    cno0 = X86_HTM_ADDR_TO_CNO(a0);
    cno1 = X86_HTM_ADDR_TO_CNO(a0 + size);
    SANITY_ASSERT(cno0 == cno1 || (cno0 + 1) == cno1);

    if (cno0 == cno1) {
      cline0 = cline1 = load_cacheline(env, cno0, false);
      if (cline0) {
        p0 = (uint8_t *)(&cline0->data[0] + X86_HTM_ADDR_CL_OFFSET(a0));
        p1 = 0;
      } else {
        p0 = (uint8_t *)((uintptr_t)a0);
        p1 = 0;
      }
    } else {
      cline0 = load_cacheline(env, cno0, false);
      cline1 = load_cacheline(env, cno1, false);
      SANITY_ASSERT(cline0 != cline1);
      split = X86_HTM_CNO_TO_ADDR(cno1) - a0;

      if (cline0)
        p0 = (uint8_t *)(&cline0->data[0] + X86_HTM_ADDR_CL_OFFSET(a0));
      else
        p0 = (uint8_t *)((uintptr_t)a0);

      if (cline1)
        p1 = (uint8_t *)(&cline1->data[0]);
      else
        p1 = (uint8_t *)((uintptr_t)a0 + split);
    }

  } else {
    p0 = (uint8_t *)((uintptr_t)a0);
    p1 = 0;
  }

  SANITY_ASSERT(size >= split);
  do_split_read(p0 + GUEST_BASE, p1 + GUEST_BASE, buf, split, size);

  switch (idx & 3) {
  case 0:
    SANITY_ASSERT(!p1);
    if (sign)
      return (target_ulong) (int8_t)buf[0];
    else
      return (target_ulong) buf[0];

  case 1:
    if (sign)
      return (target_ulong) (int16_t)tswap16(*((uint16_t *)buf));
    else
      return (target_ulong) tswap16(*((uint16_t *)buf));

  case 2:
    if (sign)
      return (target_ulong) (int32_t)tswap32(*((uint32_t *)buf));
    else
      return (target_ulong) tswap32(*((uint32_t *)buf));

  default:
  case 3:
#ifdef TARGET_X86_64
    if (sign)
      return (target_ulong) (int64_t)tswap64(*((uint64_t *)buf));
    else
      return (target_ulong) tswap64(*((uint64_t *)buf));
#else
    /* Should never happen on 32-bit targets.  */
    assert(false);
#endif
    break;
  }

  // not reached
  return 0;
}
#else
static inline target_ulong helper_htm_mem_load_helper(
    CPUX86State *env, target_ulong a0, uint32_t idx, bool sign)
{
  // need a different implementation
  assert(false);
  return 0;
}
#endif /* defined(CONFIG_USER_ONLY) */

target_ulong helper_htm_mem_loadu(
    CPUX86State *env, target_ulong a0, uint32_t idx)
{
  return helper_htm_mem_load_helper(env, a0, idx, false);
}

target_ulong helper_htm_mem_loads(
    CPUX86State *env, target_ulong a0, uint32_t idx)
{
  return helper_htm_mem_load_helper(env, a0, idx, true);
}

#if defined(CONFIG_USER_ONLY)
static inline void
do_split_write(uint8_t *p0, uint8_t *p1, const uint8_t *buf,
               uint32_t split, uint32_t size)
{
  memmove(p0, buf, split);
  if (size > split)
    memmove(p1, buf + split, size - split);
}

void helper_htm_mem_store(
    CPUX86State *env, target_ulong t0, target_ulong a0, uint32_t idx)
{
  target_ulong cno0, cno1; /* need at most two cache lines */
  CPUX86CacheLine *cline0, *cline1;

  uint8_t *p0, *p1, buf[sizeof(t0)];
  uint32_t split, size;

  cline0 = cline1 = 0;

  // split means the following:
  // the first split bytes of buf are written to [p0, p0 + split)
  // the remaining (size - split) bytes of buf are written to
  //   [p1, p1 + (size-split))

  size = mem_idx_to_size(idx);
  split = size;

  if (X86_HTM_IN_TXN(env)) {

    // convert a0 to cache line number(s)
    cno0 = X86_HTM_ADDR_TO_CNO(a0);
    cno1 = X86_HTM_ADDR_TO_CNO(a0 + size);
    SANITY_ASSERT(cno0 == cno1 || (cno0 + 1) == cno1);

    printf("helper_htm_mem_store: store %d bytes t0=(0x%llx) "
           "into addr=(0x%llx), cache_line_addr=(0x%llx)\n",
           size,
           (unsigned long long) t0,
           (unsigned long long) a0,
           (unsigned long long) X86_HTM_CNO_TO_ADDR(cno0));

    if (cno0 == cno1) {
      cline0 = cline1 = load_cacheline(env, cno0, true);
      if (!cline0) {
        // XXX: abort txn
        assert(false);
      }
      p0 = (uint8_t *)(&cline0->data[0] + X86_HTM_ADDR_CL_OFFSET(a0));
      p1 = 0;
    } else {
      cline0 = load_cacheline(env, cno0, true);
      cline1 = load_cacheline(env, cno1, true);
      if (!cline0 || !cline1) {
        // XXX: abort txn
        assert(false);
      }
      SANITY_ASSERT(cline0 != cline1);
      split = X86_HTM_CNO_TO_ADDR(cno1) - a0;
      p0 = (uint8_t *)(&cline0->data[0] + X86_HTM_ADDR_CL_OFFSET(a0));
      p1 = (uint8_t *)(&cline1->data[0]);
    }
  } else {
    p0 = (uint8_t *)((uintptr_t)a0);
    p1 = 0;
  }

  SANITY_ASSERT(size >= split);

  // see tci.c

  switch (idx & 3) {
  case 0:
    // st8
    SANITY_ASSERT(!p1);
    SANITY_ASSERT(split == 1);
    *(p0 + GUEST_BASE) = (uint8_t)t0;
    break;

  case 1:
    // st16
    *((uint16_t *)buf) = tswap16(t0);
    do_split_write(p0 + GUEST_BASE, p1 + GUEST_BASE, buf, split, size);
    break;

  case 2:
    // st32
    *((uint32_t *)buf) = tswap32(t0);
    do_split_write(p0 + GUEST_BASE, p1 + GUEST_BASE, buf, split, size);
    break;

  default:
  case 3:
#ifdef TARGET_X86_64
    // st64
    *((uint64_t *)buf) = tswap64(t0);
    do_split_write(p0 + GUEST_BASE, p1 + GUEST_BASE, buf, split, size);
#else
    /* Should never happen on 32-bit targets.  */
    assert(false);
#endif
    break;
  }
}
#else
void helper_htm_mem_store(
    CPUX86State *env, target_ulong t0, target_ulong a0, uint32_t idx)
{
  // XXX: will need a different implementation which looks at
  // soft-mmu
  assert(false);
}
#endif /* defined(CONFIG_USER_ONLY) */


CPUX86CacheLine* cpu_htm_get_free_cache_line(CPUX86State *env)
{
  CPUX86CacheLine *ret;
  if (!(ret = env->htm_free_list))
    // no more free cache lines
    return ret;
  env->htm_free_list = ret->next;
  ret->next          = 0;
  return ret;
}

void cpu_htm_return_cache_line(CPUX86State *env, CPUX86CacheLine *line)
{
  line->next         = env->htm_free_list;
  env->htm_free_list = line;
}

CPUX86CacheLine* cpu_htm_hash_table_lookup(CPUX86State *env, target_ulong cno)
{
  target_ulong h;
  CPUX86CacheLine *p;
  h = X86_HTM_CNO_HASH_FCN(cno);
  for (p = env->htm_hash_table[h % X86_HTM_NBUFENTRIES]; p; p = p->next) {
    if (p->cno == cno)
      return p;
  }
  return 0;
}

bool cpu_htm_hash_table_insert(CPUX86State *env, CPUX86CacheLine *entry)
{
  target_ulong h;
  CPUX86CacheLine **pp;
  bool found;

  h     = X86_HTM_CNO_HASH_FCN(entry->cno);
  found = 0;

  // assert that no other entry exists w/ the same entry, but
  // different pointer value
  for (pp = &env->htm_hash_table[h % X86_HTM_NBUFENTRIES]; *pp; pp = &((*pp)->next)) {
    if ((*pp)->cno == entry->cno) {
      assert((*pp) == entry);
      found = 1;
    }
  }

  if (!found) {
    entry->next = 0;
    *pp         = entry;
  }

  return !found;
}

CPUX86CacheLine* cpu_htm_hash_table_remove(CPUX86State *env, target_ulong cno)
{
  target_ulong h;
  CPUX86CacheLine **pp, *ret;
  h = X86_HTM_CNO_HASH_FCN(cno);
  for (pp = &env->htm_hash_table[h % X86_HTM_NBUFENTRIES]; *pp; pp = &((*pp)->next)) {
    if ((*pp)->cno == cno) {
      ret       = *pp;
      *pp       = (*pp)->next;
      ret->next = 0;
      return ret;
    }
  }
  return 0;
}

void cpu_htm_hash_table_iterate(CPUX86State *env, void (*fn)(CPUX86CacheLine*))
{
  int i;
  CPUX86CacheLine *p;
  for (i = 0; i < X86_HTM_NBUCKETS; i++) {
    for (p = env->htm_hash_table[i]; p; p = p->next) {
      fn(p);
    }
  }
}

void cpu_htm_hash_table_reset(CPUX86State *env)
{
  int i = 0;
  for (i = 0; i < X86_HTM_NBUFENTRIES; i++) {
    cpu_htm_return_cache_line(env, &env->htm_cache_lines[i]);
  }
  for (i = 0; i < X86_HTM_NBUCKETS; i++) {
    env->htm_hash_table[i] = 0;
  }
}
