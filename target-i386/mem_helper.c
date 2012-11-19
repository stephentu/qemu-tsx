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
#include "helper.h"

#if !defined(CONFIG_USER_ONLY)
#include "softmmu_exec.h"
#endif /* !defined(CONFIG_USER_ONLY) */

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
  }
}

void helper_xend(CPUX86State *env)
{
  printf("helper_xend()\n");
  // XXX: signal processor exception
  assert(env->htm_nest_level > 0);
  if (--env->htm_nest_level == 0) {
    printf("html region end\n");

    // XXX: commit memory changes
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

  // XXX: restore memory state

  // set high bits of EAX to imm8
  env->regs[R_EAX] |= imm8 << 24;

  // XXX: what else do we need to do to EAX?

  // go to abort handler
  env->eip = env->htm_abort_eip;
  printf("set env to go to eip=0x%llx\n", (unsigned long long) env->eip);
  printf("restored esp: 0x%llx\n", (unsigned long long) env->regs[R_ESP]);
  printf("restored ebp: 0x%llx\n", (unsigned long long) env->regs[R_EBP]);
}

target_ulong helper_htm_mem_load(
    CPUX86State *env, uint64_t a0, uint32_t idx)
{
  target_ulong cno;
  CPUX86CacheLine *cline;
  uint8_t *p;

  assert(X86_HTM_IN_TXN(env));

  printf("helper_htm_mem_load(a0=0x%llx, idx=0x%llx) in txn\n",
         (unsigned long long) a0,
         (unsigned long long) idx);

  // convert a0 to a cache line number
  cno = X86_HTM_ADDR_TO_CNO(a0);
  if ((cline = cpu_htm_hash_table_lookup(env, cno))) {
    printf("cache hit! a0=0x%llx\n", (unsigned long long) a0);
    // load from cache line
    p = (uint8_t *)(&cline->data + X86_HTM_ADDR_CL_OFFSET(a0));
  } else {
    // load from memory
    p = (uint8_t *) a0;
  }

  switch (idx & 3) {
  case 0:
    // ld8
    return (target_ulong) *p;

  case 1:
    // ld16
    return (target_ulong) *((uint16_t *)p);

  case 2:
    // ld32
    return (target_ulong) *((uint32_t *)p);

  default:
  case 3:
#ifdef TARGET_X86_64
    // ld64
    return (target_ulong) *((uint64_t *)p);

#else
    /* Should never happen on 32-bit targets.  */
    assert(false);
#endif
    break;
  }

  return 0;
}

void helper_htm_mem_store(
    CPUX86State *env, uint64_t t0, uint64_t a0, uint32_t idx)
{

  target_ulong cno;
  CPUX86CacheLine *cline;
  bool r;
  uint8_t u8, *cstart;
  uint16_t u16;
  uint32_t u32;

  assert(X86_HTM_IN_TXN(env));

  printf("helper_htm_mem_store(t0=0x%llx, a0=0x%llx, idx=0x%llx) in txn\n",
         (unsigned long long) t0,
         (unsigned long long) a0,
         (unsigned long long) idx);

  // convert a0 to a cache line number
  cno = X86_HTM_ADDR_TO_CNO(a0);

  // load the cache line into per-cpu buffer
  if (!(cline = cpu_htm_hash_table_lookup(env, cno))) {

    // not found, need to allocate a new cache line
    cline = cpu_htm_get_free_cache_line(env);
    if (!cline) {
      // XXX: abort the txn!
      assert(false);
    }

    // read the cache line from memory, to fill the buffer
    memmove(&cline->data, (void*) X86_HTM_CNO_TO_ADDR(cno), X86_CACHE_LINE_SIZE);

    cline->cno = cno;
    if (!(r = cpu_htm_hash_table_insert(env, cline)))
      assert(false);
  }

  cstart = (uint8_t *) &cline->data;

  switch (idx & 3) {
  case 0:
    // st8
    u8 = t0;
    *((uint8_t *)(cstart + X86_HTM_ADDR_CL_OFFSET(a0))) = u8;
    break;

  case 1:
    // st16
    u16 = t0;
    *((uint16_t *)(cstart + X86_HTM_ADDR_CL_OFFSET(a0))) = u16;
    break;

  case 2:
    // st32
    u32 = t0;
    *((uint32_t *)(cstart + X86_HTM_ADDR_CL_OFFSET(a0))) = u32;
    break;

  default:
  case 3:
#ifdef TARGET_X86_64
    // st64
    *((uint64_t *)(cstart + X86_HTM_ADDR_CL_OFFSET(a0))) = t0;
#else
    /* Should never happen on 32-bit targets.  */
    assert(false);
#endif
    break;
  }
}


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
