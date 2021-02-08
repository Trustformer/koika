jal x1, lbl
1: j 1b

lbl:
sw x1, 0(a0)
jal x0, x1
