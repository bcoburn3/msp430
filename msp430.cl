;emulator for the MSP430, written to help solve the final level in the Matasano/Square CTF at https://microcorruption.com/

;data structure plans:
;memory to be represented as a large array of bytes
;registers as a much smaller array of words

;some utilities, that would be in a library normally

(ql:quickload "cl-utilities")

(use-package :cl-utilities) ;purely for split-sequence

(defun hex-char-to-int (chr)
  (let ((hex-index "0123456789abcdef")
        (int-index #(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)))
    (elt int-index (position chr hex-index))))

(defun hex-string-to-int (str)
  (if (equal str "")
      0
      (let ((down-str (string-downcase str)))
	(loop for i from 0 to (- (length str) 1)
	   for res = (hex-char-to-int (elt down-str i)) then (+ (* res 16) (hex-char-to-int (elt down-str i)))
	   finally (return res)))))

(defun 4bits-to-hex-char (bits)
  (let ((hex-index "0123456789abcdef")
        (int-index #(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)))
    (elt hex-index (position bits int-index))))

(defun list-to-string (l)
  (with-output-to-string (s)
    (dolist (c l)
      (princ c s))))

(defun int-to-hex-string (int)
  (list-to-string
   (loop for i = int then (/ (- i (mod i 16)) 16)
       while (>= i 1)
       with res = '()
       do (push (4bits-to-hex-char (mod i 16)) res)
       finally (return res))))

;global variables

(defvar *log-stream* *standard-output*)

(defvar *reg* (make-array 16 :element-type '(UNSIGNED-BYTE 16)))

(defvar *mem* (make-array 65536 :element-type '(UNSIGNED-BYTE 8)))

(defvar *input*)

(defvar *console* "console:")

(defvar *err*)

(defvar *dep* nil)

(defvar *dep-table* 0)

(defvar *unlocked* nil)

(defun log-line (arg)
  (if (integerp arg)
      (print (format nil "~4,'0x" arg) *log-stream*)
      (print arg *log-stream*))
  t)


;some utility functions specific to the emulator
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
;  (log-line "get-mem")
 ; (log-line idx)
  ;(log-line (bytes-to-word (mem idx) (mem (+ idx 1))))
  (bytes-to-word (mem idx) (mem (+ idx 1))))

(defun set-mem (idx int b-w)
  (log-line "set-mem")
 (log-line (get-mem idx))
  (log-line "idx")
 (log-line idx)
  (let* ((low (mod int 256))
	 (high (/ (- int low) 256)))
    (if (= b-w 0)
	(setf (elt *mem* idx) low)
	(setf (elt *mem* idx) low
	      (elt *mem* (+ idx 1)) high)))
  (log-line "res")
  (log-line (get-mem idx))
  t)

(defun mem-fun (idx)
  (function (lambda (int b-w) (set-mem idx int b-w))))

(defun set-reg (idx int)
  (setf (elt *reg* idx) int))
;  (let ((low (ldb (byte 8 0) int))
;	(high (ldb (byte 8 8) int)))
;    (setf (elt *reg* idx) (+ (dpb low (byte 8 8) 0)
;			     (dpb high (byte 8 0) 0)))))

(defun reg-fun (idx)
  (function (lambda (int b-w) 
    (set-reg idx (trim-bw int b-w)))))

(defun get-reg (idx)
  (elt *reg* idx))
;  (let ((val (reg idx)))
;    (let ((low (ldb (byte 8 0) val))
;	  (high (ldb (byte 8 8) val)))
;      (+ (dpb low (byte 8 8) 0)
;	 (dpb high (byte 8 0) 0)))))

(defun inc-reg (idx)
  (incf (elt *reg* idx) 2))
;  (set-reg idx (+ 2 (get-reg idx))))

(defun dec-reg (idx)
  (incf (elt *reg* idx) -2))
;  (set-reg idx (+ -2 (get-reg idx))))
  
(defun dep-set (page val)
  (setf *dep-table* (dpb val (byte 1 page) *dep-table*)))

(defun dep-check (page)
  (ldb (byte 1 page) *dep-table*))

(defun nullp (val b-w)
  (if (= (trim-bw val b-w) 0)
      1 
      0))

(defun negp (val b-w)
  (ldb (byte 1 (+ b-w 7)) val))

(defun trim-bw (val b-w)
  (ldb (byte (+ b-w 8) 0) val))

;start of actual emulator
(defun main ()
  (setf *reg* (make-array 16 :element-type '(unsigned-byte 16)))
  (set-reg 0 #x4400)
  (loop repeat 1000000
     while (emu-step)
       do (if *unlocked*
	      (return-from main "victory"))))

(defun emu-step ()
  (let* ((pc (get-reg 0))
	 (bytes (subseq *mem* pc (+ pc 6))))
    (log-line bytes)
    (log-line "PC")
    (log-line pc)
    (log-line "sp")
    (log-line (get-reg 1))
    (log-line "sr")
    (log-line (get-reg 2))
    (log-line "registers")
    (log-line *reg*)
    (cond ((oddp pc) (progn (setf *err* "PC unalligned")
			    (return-from emu-step nil)))
	  ((= (ldb (byte 1 4) (get-reg 2)) 1) (progn (setf *err* "cpu-off set")
						 (return-from emu-step nil)))
	  ((= pc 16) (int-handler (ldb (byte 7 8) (get-reg 2))))
	  ((= (bytes-to-word (elt bytes 0) (elt bytes 1)) 0)
	   (progn (setf *err* "zero instruction")
			    (return-from emu-step nil)))
	  (t (instruction-decode bytes)))
    ))
							     
(defun int-handler (type)
  (log-line "interrupt")
  (log-line (subseq *mem* (get-reg 1) (+ 16 (get-reg 1))))
  (let ((arg1 (get-mem (+ 8 (get-reg 1))))
	(arg2 (get-mem (+ 10 (get-reg 1)))))
    (cond ((= type 0) (setf *console* (concatenate 'string *console* 
						   (list (code-char (ldb (byte 8 0) arg1))))))
	  ((= type 2) (getsn arg1 arg2))
	  ((= type 3) (dep-set arg1 arg2))
	  ((= type 4) (set-reg 15 (random 65536 (make-random-state t))))
	  ((= type #x7d) (set-mem arg2 0 0)) ;assume password is always false
	  ((= type #x7e) t) ;assume passsword is always false
	  ((= type #x7f) (setf *unlocked* t)))
    (set-reg 0 (get-mem (get-reg 1)))
    (inc-reg 1)))

(defun getsn (start num)
  (log-line "getsn")
  (log-line start)
  (log-line num)
  (log-line (car *input*))
  (let ((cur-input (car *input*)))
    (loop for i from 0 to (- (/ (length cur-input) 2) 1)
       while (<= i num)
       for char = (hex-string-to-int (subseq cur-input (* i 2) (* (+ i 1) 2)))
       do (set-mem (+ start i) char 0)))
  (setf *input* (cdr *input*)))
  

(defun instruction-decode (bytes)
  ;bytes to be an arry of 6 bytes, to allow for the longest possible instruction
  ;this is the entry point into the instruction decoding, will eventually call the 
  ;appropriate function
  (let ((instn (bytes-to-word (elt bytes 0) (elt bytes 1)))
	(data1 (bytes-to-word (elt bytes 2) (elt bytes 3)))
	(data2 (bytes-to-word (elt bytes 4) (elt bytes 5))))
    (cond ((= (ldb (byte 4 12) instn) 1) (single-decode instn data1))
	  ((= (ldb (byte 3 13) instn) 1) (jump-decode instn))
	  ((>= (ldb (byte 4 12) instn) 4) (double-decode instn data1 data2)))))

(defun address-decode (ad dest data b-w)
  (log-line ad)
  (log-line dest)
  (log-line data)
  ;decodes an address for a single operand instruction
  ;returns an integer representing the current value and a function that sets the new value
  (if (or (= dest 2) (= dest 3))
      (if (= dest 2)
	  (cond ((= ad 0) (values (get-reg dest)
				  (reg-fun dest)
				  0)) ;register mode
		((= ad 1) (progn (inc-reg 0)
				 (values (get-mem data)
					 (mem-fun data)
					 1)));absolute mode
		((= ad 2) (values 4 (reg-fun dest) 0)) ;represents a constant, can't set things
		((= ad 3) (values 8 (reg-fun dest) 0)) ;as above
		(t 'nil)) 
	  (cond ((= ad 0) (values 0 (reg-fun dest) 0)) ;dest = 3
		((= ad 1) (values 1 (reg-fun dest) 0))
		((= ad 2) (values 2 (reg-fun dest) 0))
		((= ad 3) (values 65535 (reg-fun dest) 0))
		(t 'nil)))
      (cond ((= ad 0) (values (get-reg dest)
			      (reg-fun dest)
			      0)) ;register mode
	    ((= ad 1) (let ((idx (mod+ (get-reg dest) data)))
			(inc-reg 0)
			(values (get-mem idx)
				(mem-fun idx)
				1))) ;index mode
	    ((= ad 2) (values (get-mem (get-reg dest))
			      (mem-fun (get-reg dest))
			      0)) ;indirect mode
	    ((= ad 3) (progn (addr-increment dest b-w)
			     (values (get-mem (- (get-reg dest) (if (= dest 0)
								    2
								    (+ 1 (/ b-w 8)))))
				     (mem-fun (- (get-reg dest) (if (= dest 0)
								    2
								    (+ 1 (/ b-w 8)))))
				     0))) ;indirect mode with increment
	    (t 'nil))))

(defun addr-increment (idx b-w)
  (if (= 0 idx)
      (incf (elt *reg* idx) 2)
      (incf (elt *reg* idx) (+ 1 (/ b-w 8)))))

(defun single-decode (instn data)
  (log-line "single-op")
  (inc-reg 0)
  ;decodes and calls a single operand instruction
  (let ((opcode (ldb (byte 3 7) instn))
	(ad (ldb (byte 2 4) instn))
	(dest (ldb (byte 4 0) instn))
	(b-w (if (= 1 (ldb (byte 1 6) instn))
		 0
		 8)))
    (multiple-value-bind (value set-fun)
	(address-decode ad dest data b-w)
      ;(log-line value)
      ;(log-line set-fun)
      (cond ((= opcode 0) (rrc value set-fun b-w))
	    ((= opcode 1) (swpb value set-fun))
	    ((= opcode 2) (rra value set-fun b-w))
	    ((= opcode 3)  (sxt value set-fun))
	    ((= opcode 4) (psh value set-fun b-w))
	    ((= opcode 5) (call value set-fun))
	    (t 'nil)))))
	      ;RETI isn't implemented because it's not in the CTF

(defun rrc (value set-fun b-w)
  (log-line "rrc")
  (let ((carry (ldb (byte 1 0) value))
	(tmp (ash (trim-bw value b-w) -1)))
    (let ((res (dpb (get-c) (byte 1 (+ b-w 7)) tmp)))
      (funcall set-fun res b-w)
      (set-v 0)
      (set-c carry)
      (if (= (negp res b-w) 1)
	  (set-n 1))
      (if (= (nullp res b-w) 0)
	  (set-z 0)))))

(defun swpb (value set-fun)
  (log-line "swpb")
  (let ((low (ldb (byte 8 8) value))
	(high (ldb (byte 8 0) value)))
    (funcall set-fun (+ (* 256 high) low) 8)))

(defun rra (value set-fun b-w)
  (log-line "rra")
  (let ((res (ash (trim-bw value b-w) -1)))
    (funcall set-fun res b-w)
    (if (= (negp res b-w) 1)
	(set-n 1))
    (set-v 0)
    (set-z 0)))

(defun sxt (value set-fun)
  (log-line "sxt")
  (let ((res (dpb (* 255 (ldb (byte 1 7) value)) (byte 8 8) value)))
    (funcall set-fun res 8)
    (set-c (if (= res 0)
	       0
	       1))
    (set-v 0)
    (set-n (negp res 8))
    (set-z (nullp res 8))))

(defun psh (value set-fun b-w)
  (log-line "psh")
  (log-line value)
  (dec-reg 1)
  (set-mem (get-reg 1) value b-w))

(defun call (value set-fun)
  (log-line "call")
  (log-line value)
  (psh (get-reg 0) nil 8)
  (set-reg 0 value))

(defun jump-decode (instn)
  (log-line "jump")
  (log-line instn)
  (log-line (get-reg 2))
  (let ((type (ldb (byte 3 10) instn))
	(offset (ldb (byte 10 0) instn))
	(z (flag 1))
	(c (flag 0))
	(n (flag 2))
	(v (flag 8)))
    (cond ((= type 0) (if (= z 0) 
			  (jmp offset)
			  (inc-reg 0)))
	  ((= type 1) (if (= z 1) 
			  (jmp offset)
			  (inc-reg 0)))
	  ((= type 2) (if (= c 0) 
			  (jmp offset)
			  (inc-reg 0)))
	  ((= type 3) (if (= c 1) (jmp offset)
			  (inc-reg 0)))
	  ((= type 4) (if (= n 1) (jmp offset)
			  (inc-reg 0)))
	  ((= type 5) (if (= n v) (jmp offset)
			  (inc-reg 0)))
	  ((= type 6) (if (/= n v) (jmp offset)
			  (inc-reg 0)))
	  ((= type 7) (jmp offset)))))

(defun jmp (offset)
  (log-line offset)
  (log-line (ldb (byte 9 0) offset))
  (log-line (* (ldb (byte 1 9) offset) 1024))
  (log-line (- (* 2 (- (ldb (byte 9 0) offset)
		       (* (ldb (byte 1 9) offset) 512)))))
  (set-reg 0 (+ (get-reg 0) 2
		(* 2 (- (ldb (byte 9 0) offset)
			(* (ldb (byte 1 9) offset) 512)))))
  t)

(defun double-decode (instn data1 data2)
  (log-line "double-op")
  (inc-reg 0)
  (let ((opcode (ldb (byte 4 12) instn))
	(source (ldb (byte 4 8) instn))
	(ad (ldb (byte 1 7) instn))
	(as (ldb (byte 2 4) instn))
	(dest (ldb (byte 4 0) instn))
	(b-w (if (= 1 (ldb (byte 1 6) instn))
		 0
		 8)))
    (multiple-value-bind (source-val source-fun data-offset)
	(address-decode as source data1 b-w)
      (multiple-value-bind (dest-val dest-fun junk-val)
	  (address-decode ad dest (if (= data-offset 1)
				      data2    ;use the second extension word if
				      data1)
			  b-w)  ;the first was used in the source
;      (let* ((source-lst (multiple-value-list (address-decode as source data1)))
;	     (source-val (car source-lst)))
	;(log-line source-lst)
	(log-line "source")
	(log-line source-val)
	(log-line "dest")
	(log-line dest-val)
	(cond ((= opcode 4) (mov source-val dest-fun b-w))
	      ((= opcode 5) (add source-val dest-val dest-fun b-w))
	      ((= opcode 6) (addc source-val dest-val dest-fun b-w))
	      ((= opcode 7) (subc source-val dest-val dest-fun b-w))
	      ((= opcode 8) (sub source-val dest-val dest-fun b-w))
	      ((= opcode 9) (cmp source-val dest-val b-w))
	      ((= opcode 10) (dadd source-val dest-val dest-fun b-w))
	      ((= opcode 11) (emu-bit source-val dest-val b-w))
	      ((= opcode 12) (bic source-val dest-val dest-fun b-w))
	      ((= opcode 13) (bis source-val dest-val dest-fun b-w))
	      ((= opcode 14) (xor source-val dest-val dest-fun b-w))
	      ((= opcode 15) (emu-and source-val dest-val dest-fun b-w))
	      (t 'nil))))))

(defun mov (val dest-fun b-w)
  (log-line "mov")
 (log-line  val)
  (log-line dest-fun)
  (log-line b-w)
  (funcall dest-fun val b-w))

(defun add-flags (res b-w)
  (set-c (ldb (byte 1 (+ b-w 8)) res))
  (set-v 0)
  (set-n (negp res b-w))
  (set-z (nullp res b-w)))

(defun add (source-val dest-val dest-fun b-w)
  (log-line "add")
  (log-line "source")
  (log-line source-val)
  (log-line "dest")
  (log-line dest-val)
  (log-line b-w)
  (let ((res (+ (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun addc (source-val dest-val dest-fun b-w)
  (log-line "addc")
  (let ((res (+ (trim-bw source-val b-w) (trim-bw dest-val b-w) (get-c))))
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun subc (source-val dest-val dest-fun b-w)
  (log-line "subc")
  (let ((res (+ (trim-bw dest-val b-w) (lognot (trim-bw source-val b-w)) (get-c) 1))) ;random +1 for bug compat
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun sub (source-val dest-val dest-fun b-w)
  (log-line "sub")
  (let ((res (+ (trim-bw dest-val b-w) (trim-bw (lognot source-val) b-w) 1)))
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun cmp (source-val dest-val b-w)
  (log-line "cmp")
  (log-line  source-val)
  (log-line  dest-val)
  (log-line b-w)
  (let ((res (+ (trim-bw dest-val b-w) (trim-bw (lognot source-val) b-w) 1)))
    (add-flags res b-w))
  (log-line (get-reg 2)))

(defun dadd (source-val dest-val dest-fun b-w)
  (log-line "dadd")
  (let ((trim-s (trim-bw source-val b-w))
	(trim-d (trim-bw dest-val b-w)))
    (let ((res (loop for i in (list 0 4 8 12)
		  for c = 0 then (if (>= tmp 10)
				     1
				     0)
		  for tmp = (+ (ldb (byte 4 i) trim-s)
			       (ldb (byte 4 i) trim-d)
			       c)
		  for tmp2 = (if (>= tmp 10)
				 (- tmp 10)
				 tmp)
		  for val = tmp2 then (dpb tmp2 (byte 4 i) val)
		  finally (progn (set-c c)
				 (if (ldb (byte 1 3) tmp)
				     (set-n 1))
				 (return val)))))
      (funcall dest-fun res b-w))))

(defun emu-bit (source-val dest-val b-w)
  (log-line "emu-bit")
  (let ((res (logand (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (set-v 0)
    (set-n (ldb (byte 1 (+ b-w 7)) res))
    (set-z (nullp res b-w))
    (set-c (nullp res b-w))))

(defun bic (source-val dest-val dest-fun b-w)
  (log-line "bic")
  (let ((res (logand (lognot (trim-bw source-val b-w)) (trim-bw dest-val b-w))))
    (funcall dest-fun res b-w)))

(defun bis (source-val dest-val dest-fun b-w)
  (log-line "bis")
  (funcall dest-fun (logior (trim-bw source-val b-w) (trim-bw dest-val b-w)) b-w))

(defun xor (source-val dest-val dest-fun b-w)
  (log-line "xor")
  (let ((res (logxor (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (funcall dest-fun res b-w)
    (set-v 0)
    (set-n (ldb (byte 1 (+ b-w 7)) res))
    (set-z (nullp res b-w))
    (set-c (nullp res b-w))))

(defun emu-and (source-val dest-val dest-fun b-w)
  (log-line "emu-and")
  (let ((res (logand (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (funcall dest-fun res b-w)
    (set-v 0)
    (set-n (ldb (byte 1 (+ b-w 7)) res))
    (set-z (nullp res b-w))
    (set-c (nullp res b-w))))

;start of file importing code

(defun import-file (file)
  (setf *mem* (make-array 65536 :element-type '(unsigned-byte 8)))
  (with-open-file (in file)
    (loop for line = (read-line in nil)
       while line
       do (if (not (equal #\* (elt line 8)))
	      (let* ((split-line (split-sequence #\: line))
		     (offset (hex-string-to-int (car split-line)))
		     (blocks (subseq (split-sequence #\space (cadr split-line)) 3 11)))
		(loop for i from 0 to 7
		   for block = (elt blocks i)
		   do (set-mem (+ offset (* i 2)) (block-val block) 8)))))))

(defun block-val (str)
  (hex-string-to-int 
   (concatenate 'string (subseq str 2 4) (subseq str 0 2))))

(defun reset ()
  (setf *reg* (make-array 16 :element-type '(UNSIGNED-BYTE 16)))
  (setf *mem* (make-array 65536 :element-type '(UNSIGNED-BYTE 8)))
  (setf *err* "null")
  (setf *console* "console:")
  (setf *unlocked* nil))

(defun run-level (file-name input)
  (reset)
  (setf *log-stream* (open "C:\\ben\\log.txt" :direction :output :if-exists :supersede :sharing :external))
  ;(setf *log-stream* *standard-output*)
  (print "start of run")
  (import-file file-name)
  (setf *input* input)
  (main)
  (print file-name)
  (print *console*)
  (print "error:")
  (print *err*)
  (print "unlocked?")
  (print *unlocked*))
