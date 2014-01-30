;emulator for the MSP430, written to help solve the final level in the Matasano/Square CTF at https://microcorruption.com/

;data structure plans:
;memory to be represented as a large array of bytes
;registers as a much smaller array of words

(defvar *reg* (make-array 16 :element-type '(UNSIGNED-BYTE 16)))

;(setf *reg* (make-array 16 :element-type '(unsigned-byte 16)))

(defvar *mem* (make-array 65536 :element-type '(UNSIGNED-BYTE 8)))

(defun mem (idx)
  (elt *mem* idx))

(defun reg (idx)
  (elt *reg* idx))

(defun flag (idx)
  (ldb (byte 1 idx) (reg 2)))

(defun get-c ()
  (ldb (byte 1 0) (reg 2)))

(defun set-c (int)
  (setf (elt *reg* 2) (dpb int (byte 1 0) (reg 2))))

(defun get-z ()
  (ldb (byte 1 1) (reg 2)))

(defun set-z (int)
  (setf (elt *reg* 2) (dpb int (byte 1 1) (reg 2))))

(defun get-n ()
  (ldb (byte 1 2) (reg 2)))

(defun set-n (int)
  (setf (elt *reg* 2) (dpb int (byte 1 2) (reg 2))))

(defun get-v ()
  (ldb (byte 1 8) (reg 2)))

(defun set-v (int)
  (setf (elt *reg* 2) (dpb int (byte 1 8) (reg 2))))

(defun bytes-to-word (low high)
  (+ (* 256 high) low))

(defun mod+ (&rest args)
  (mod (reduce #'+ args) 65536))

(defun mod* (&rest args)
  (mod (reduce #'* args) 65536))

(defun get-mem (idx)
  (+ (* 256 (mem (+ idx 1))) (mem idx)))

(defun set-mem (idx int)
  (let* ((low (mod int 256))
	 (high (/ (- int low) 256)))
    (setf (elt *mem* idx) low
	  (elt *mem* (+ idx 1)) high)))

(defun mem-fun (idx)
  (function (lambda (int) (set-mem idx (mod int 65536)))))

(defun reg-fun (idx)
  (function (lambda (int) (setf (elt *reg* idx) (mod int 65536)))))

(defun nullp (val)
  (if (= val 0)
      1
      0))

(defun negp (val)
  (ldb (byte 1 15) val))



(defun instruction-decode (bytes)
  ;bytes to be an arry of 6 bytes, to allow for the longest possible instruction
  ;this is the entry point into the instruction decoding, will eventually call the 
  ;appropriate function
  (let ((instn (bytes-to-word (elt bytes 0) (elt bytes 1)))
	(data1 (bytes-to-word (elt bytes 2) (elt bytes 3)))
	(data2 (bytes-to-word (elt bytes 4) (elt bytes 5))))
    (cond ((= (ldb (byte 4 12) instn)) (single-decode instn data1))
	  ((= (ldb (byte 3 13) instn)) (jump-decode instn))
	  ((>= (ldb (byte 4 12) instn)) (double-decode instn data1 data2)))))

(defun address-decode (ad dest data)
  ;decodes an address for a single operand instruction
  ;returns an integer representing the current value and a function that sets the new value
  (if (or (= dest 2) (= dest 3))
      (if (= dest 2)
	  (cond ((= ad 0) (values (reg dest)
				  (reg-fun dest))) ;register mode
		((= ad 1) (values (get-mem data)
				  (mem-fun data))) ;absolute mode
		((= ad 2) (values 4 4)) ;represents a constant, can't set things
		((= ad 3) (values 8 8))) ;as above
	  (cond ((= ad 0) (values 0 0))
		((= ad 1) (values 1 1))
		((= ad 2) (values 2 2))
		((= ad 3) (values 65535 65535))))
      (cond ((= ad 0) (values (reg dest)
			      (reg-fun dest))) ;register mode
	    ((= ad 1) (let ((idx (mod+ (reg dest) data)))
			(values (get-mem idx)
				(mem-fun idx)))) ;index mode
	    ((= ad 2) (values (get-mem (reg dest))
			      (mem-fun (reg dest)))) ;indirect mode
	    ((= ad 3) (progn (incf (elt *reg* dest) 2)
			     (values (get-mem (- (reg dest) 2))
				     (mem-fun (- (reg dest) 2)))))))) ;indirect mode with increment

(defun single-decode (instn data)
  ;decodes and calls a single operand instruction
  (let ((opcode (ldb (byte 3 7) instn))
	(ad (ldb (byte 2 4) instn))
	(dest (ldb (byte 4 0) instn)))
    (multiple-value-bind (value set-fun)
	(address-decode ad dest data)
      (cond ((= opcode 0) (rrc value set-fun))
	    ((= opcode 1) (swpb value set-fun))
	    ((= opcode 2) (rra value set-fun))
	    ((= opcode 3) (sxt value set-fun))
	    ((= opcode 4) (psh value set-fun))
	    ((= opcode 5) (call value set-fun))))))
	      ;RETI isn't implemented because it's not in the CTF

(defun rrc (value set-fun)
  (let ((carry (ldb (byte 1 0) value))
	(tmp (ash value -1)))
    (let ((res (dpb (get-c) (byte 1 15) tmp)))
      (funcall set-fun res)
      (set-v (if (and (= (get-c) 1)
		      (= (ldb (byte 1 15) value)))
		 1
		 0))
      (set-c carry)
      (set-n (negp res))
      (set-z (nullp res)))))

(defun swpb (value set-fun)
  (let ((low (ldb (byte 8 8) value))
	(high (ldb (byte 8 0) value)))
    (funcall set-fun (+ (* 256 high) low))))

(defun rra (value set-fun)
  (let ((res (ash value -1)))
    (funcall set-fun res)
    (set-c (ldb (byte 1 0) value))
    (set-n (negp res))
    (set-v 0)
    (set-z (nullp res))))

(defun sxt (value set-fun)
  (let ((res (dpb (* 255 (ldb (byte 1 7) value)) (byte 8 8) value)))
    (funcall set-fun res)
    (set-c (if (= res 0)
	       0
	       1))
    (set-v 0)
    (set-n (negp res))
    (set-z (nullp res))))

(defun psh (value set-fun)
  (setf (elt *mem* (reg 1)) value)
  (incf (elt *reg* 1) -2))

(defun call (value set-fun)
  (psh (reg 0) 'nil)
  (setf (elt *reg* 0) value))

(defun jump-decode (instn)
  (let ((type (ldb (byte 3 10) instn))
	(offset (ldb (byte 10 0) instn))
	(z (flag 1))
	(c (flag 0))
	(n (flag 2))
	(v (flag 8)))
    (cond ((= type 0) (if (= z 0) (jmp offset)))
	  ((= type 1) (if (= z 1) (jmp offset)))
	  ((= type 2) (if (= c 0) (jmp offset)))
	  ((= type 3) (if (= c 1) (jmp offset)))
	  ((= type 4) (if (= n 1) (jmp offset)))
	  ((= type 5) (if (= n v) (jmp offset)))
	  ((= type 6) (if (/= n v) (jmp offset)))
	  ((= type 7) (jmp offset)))))

(defun jmp (offset)
  (setf (elt *reg* 0) (+ (reg 0) 2
		   (- (ldb (byte 9 0) offset)
		      (* (ldb (byte 1 9) offset) 1024))))
  t)

(defun double-decode (instn data1 data2)
  (let ((opcode (ldb (byte 4 12) instn))
	(source (ldb (byte 4 8) instn))
	(ad (ldb (byte 1 7) instn))
	(as (ldb (byte 2 4) instn))
	(dest (ldb (byte 4 0) instn)))
    (multiple-value-bind (dest-val dest-fun)
	(address-decode ad dest data2)
      (multiple-value-bind (source-val source-fun)
	  (address-decode as source data1)
	(cond ((= opcode 4) (mov source-val dest-fun))
	      ((= opcode 5) (add source-val dest-val dest-fun))
	      ((= opcode 6) (addc source-val dest-val dest-fun))
	      ((= opcode 7) (subc source-val dest-val dest-fun))
	      ((= opcode 8) (sub source-val dest-val dest-fun))
	      ((= opcode 9) (cmp source-val dest-val))
	      ((= opcode 10) (dadd source-val dest-val dest-fun))
	      ((= opcode 11) (emu-bit source-val dest-val))
	      ((= opcode 12) (bic source-val dest-val dest-fun))
	      ((= opcode 13) (bis source-val dest-val dest-fun))
	      ((= opcode 14) (xor source-val dest-val dest-fun))
	      ((= opcode 15) (emu-and source-val dest-val dest-fun)))))))

(defun mov (val dest-fun)
  (funcall dest-fun val))

(defun add-flags (res)
  (set-c (ldb (byte 1 16) res))
  (set-v (ldb (byte 1 16) res))
  (set-n (negp res))
  (set-z (nullp res)))

(defun add (source-val dest-val dest-fun)
  (let ((res (+ source-val dest-val)))
    (funcall dest-fun (mod res 65536))
    (add-flags res)))

(defun addc (source-val dest-val dest-fun)
  (let ((res (+ source-val dest-val (get-c))))
    (funcall dest-fun (mod res 65536))
    (add-flags res)))

(defun subc (source-val dest-val dest-fun)
  (let ((res (+ dest-val (lognot source-val) (get-c) 1))) ;random +1 for bug compat
    (funcall dest-fun (mod res 65536))
    (add-flags res)))

(defun sub (source-val dest-val dest-fun)
  (let ((res (+ dest-val (lognot source-val) 1)))
    (funcall dest-fun (mod res 65536))
    (add-flags res)))

(defun cmp (source-val dest-val)
  (let ((res (+ dest-val (lognot source-val) 1)))
    (add-flags res)))

(defun dadd (source-val dest-val dest-fun)
  (let ((res (loop for i in (list 0 4 8 12)
		for c = 0 then (if (>= tmp 10)
				   1
				   0)
		for tmp = (+ (ldb (byte 4 i) source-val)
			     (ldb (byte 4 i) dest-val)
			     c)
		for tmp2 = (if (>= tmp 10)
			      (- tmp 10)
			      tmp)
		for val = tmp2 then (dpb tmp2 (byte 4 i) val)
		finally (progn (set-c c)
			       (if (ldb (byte 1 3) tmp)
				   (set-n 1))
			       (return val)))))
    (funcall dest-fun res)))

(defun emu-bit (source-val dest-val)
  (let ((res (logand source-val dest-val)))
    (set-v 0)
    (set-n (ldb (byte 1 15) res))
    (set-z (nullp res))
    (set-c (nullp res))))

(defun bic (source-val dest-val dest-fun)
  (let ((res (logand (lognot source-val) dest-val)))
    (funcall dest-fun res)))

(defun bis (source-val dest-val dest-fun)
  (funcall dest-fun (logior source-val dest-val)))

(defun xor (source-val dest-val dest-fun)
  (let ((res (logxor source-val dest-val)))
    (funcall dest-fun res)
    (set-v (* (ldb (byte 1 15) source-val)
	      (ldb (byte 1 15) dest-val)))
    (set-n (ldb (byte 1 15) res))
    (set-z (nullp res))
    (set-c (nullp res))))

(defun emu-and (source-val dest-val dest-fun)
  (let ((res (logand source-val dest-val)))
    (funcall dest-fun res)
    (set-v 0)
    (set-n (ldb (byte 1 15) res))
    (set-z (nullp res))
    (set-c (nullp res))))

(let ((test2 19))
  (print (lognot test2)))
