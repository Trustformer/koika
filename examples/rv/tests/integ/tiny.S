  .globl _start
_start:
  li sp, 0x2000
  la a0, hello_string
  call putchars
  li a1, 0x40001000
  sw zero, 0(a1)

loop:
  j loop


putchars:
  mv t0, ra
  mv a2, a0
  li a1, 0x40000000
  .start_loop:
  lb a0, 0(a2)
  beq a0, zero, .end_putchars
  sw a0, 0(a1)
  addi a2, a2, 1
  j .start_loop
  .end_putchars:
  mv ra, t0
  ret



hello_string:
  .ascii "Bonjour\r\n"
