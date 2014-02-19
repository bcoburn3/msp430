;emulator for the MSP430, written to help solve the final level in the Matasano/Square CTF at https://microcorruption.com/

;data structure plans:
;memory to be represented as a large array of bytes
;registers as a much smaller array of words

(ql:quickload "cl-utilities")

(use-package :cl-utilities) ;purely for split-sequence

(defvar *log-stream* *standard-output*)

(defun log-text (&rest args)
  (print (reduce #'(lambda (current next)
		     (if (integerp next)
			 (concatenate 'string current ": " (format nil "~4,'0x" next))
			 (concatenate 'string current next)))
		 args
		 :initial-value "")
	 *log-stream*)
  t)

(defvar *reg* (make-array 16 :element-type '(UNSIGNED-BYTE 16)))

(defvar *mem* (make-array 65536 :element-type '(UNSIGNED-BYTE 8)))

(defvar *input*)

(defvar *console* "console:")

(defvar *err*)

(defvar *dep* nil)

(defvar *dep-table* 0)

(defvar *unlocked* nil)

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
  ;;(print "get-mem")
  ;(format t "~4,'0x" idx)
  ;(print (bytes-to-word (mem idx) (mem (+ idx 1))))
  (bytes-to-word (mem idx) (mem (+ idx 1))))

(defun set-mem (idx int b-w)
  (log-text "set-mem" (get-mem idx))
  (log-text "idx" idx)
  (let* ((low (mod int 256))
	 (high (/ (- int low) 256)))
    (if (= b-w 0)
	(setf (elt *mem* idx) low)
	(setf (elt *mem* idx) low
	      (elt *mem* (+ idx 1)) high)))
  (log-text "res" (get-mem idx))
  t)

(defun mem-fun (idx)
  (log-text "mem-fun" idx)
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
    (print (map 'list #'(lambda (x) (format nil "~2,'0x" x)) bytes) *log-stream*)
    (print (map 'list #'(lambda (x) (format nil "~4,'0x" x)) *reg*) *log-stream*)
    (log-text "PC" pc)
    (log-text "SP" (get-reg 1))
    (log-text "SR" (get-reg 2))
    (cond ((oddp pc) (progn (setf *err* "PC unalligned")
			    (return-from emu-step nil)))
	  ((= (ldb (byte 1 4) (get-reg 2)) 1) (progn (setf *err* "cpu-off set")
						 (return-from emu-step nil)))
	  ((= pc 16) (int-handler (ldb (byte 7 8) (get-reg 2))))
	  ((= (bytes-to-word (elt bytes 0) (elt bytes 1)) 0)
	   (progn (setf *err* "zero instruction")
			    (return-from emu-step nil)))
	  (t (instruction-decode bytes)))))

(defun int-handler (type)
  ;(print "interrupt")
  ;(print (subseq *mem* (get-reg 1) (+ 16 (get-reg 1))))
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
  ;(print "getsn")
  ;(format t "~4,'0x" start)
  ;(print num)
  ;(print (car *input*))
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
  (log-text "AD" ad)
  (log-text "dest" dest)
  (log-text "ext-word" data)
  ;decodes an address for a single operand instruction
  ;returns:
  ;an integer representing the current value
  ;a function that sets the new value
  ;t if an extension word was used, nil otherwise
  (if (or (= dest 2) (= dest 3))
      (if (= dest 2)
	  (cond ((= ad 0) (values (get-reg dest)
				  (reg-fun dest)
				  nil)) ;register mode
		((= ad 1) (progn (inc-reg 0)
				 (values (get-mem data)
					 (mem-fun data)
					 t)));absolute mode
		((= ad 2) (values 4 (reg-fun dest) nil)) ;represents a constant, can't set things
		((= ad 3) (values 8 (reg-fun dest) nil)) ;as above
		(t 'nil)) 
	  (cond ((= ad 0) (values 0 (reg-fun dest) nil)) ;dest = 3
		((= ad 1) (values 1 (reg-fun dest) nil))
		((= ad 2) (values 2 (reg-fun dest) nil))
		((= ad 3) (values 65535 (reg-fun dest) nil))
		(t 'nil)))
      (cond ((= ad 0) (values (get-reg dest)
			      (reg-fun dest)
			      nil)) ;register mode
	    ((= ad 1) (let ((idx (mod+ (get-reg dest) data)))
			(inc-reg 0)
			(values (get-mem idx)
				(mem-fun idx)
				t))) ;index mode
	    ((= ad 2) (values (get-mem (get-reg dest))
			      (mem-fun (get-reg dest))
			      nil)) ;indirect mode
	    ((= ad 3) (progn (addr-increment dest b-w)
			     (values (get-mem (- (get-reg dest) (if (= dest 0)
								    2
								    (+ 1 (/ b-w 8)))))
				     (mem-fun (- (get-reg dest) (if (= dest 0)
								    2
								    (+ 1 (/ b-w 8)))))
				     t))) ;indirect mode with increment
	    (t 'nil))))

(defun addr-increment (idx b-w)
  (if (= 0 idx)
      (incf (elt *reg* idx) 2)
      (incf (elt *reg* idx) (+ 1 (/ b-w 8)))))

(defun single-decode (instn data)
  (log-text "single-op")
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
      ;(print value)
      ;(print set-fun)
      (cond ((= opcode 0) (rrc value set-fun b-w))
	    ((= opcode 1) (swpb value set-fun))
	    ((= opcode 2) (rra value set-fun b-w))
	    ((= opcode 3)  (sxt value set-fun))
	    ((= opcode 4) (psh value set-fun b-w))
	    ((= opcode 5) (call value set-fun))
	    (t 'nil)))))
	      ;RETI isn't implemented because it's not in the CTF

(defun rrc (value set-fun b-w)
  (log-text "rrc")
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
  (log-text "swpb")
  (let ((low (ldb (byte 8 8) value))
	(high (ldb (byte 8 0) value)))
    (funcall set-fun (+ (* 256 high) low) 8)))

(defun rra (value set-fun b-w)
  (log-text "rra")
  (let ((res (ash (trim-bw value b-w) -1)))
    (funcall set-fun res b-w)
    (if (= (negp res b-w) 1)
	(set-n 1))
    (set-v 0)
    (set-z 0)))

(defun sxt (value set-fun)
(log-text "sxt")
  (let ((res (dpb (* 255 (ldb (byte 1 7) value)) (byte 8 8) value)))
    (funcall set-fun res 8)
    (set-c (if (= res 0)
	       0
	       1))
    (set-v 0)
    (set-n (negp res 8))
    (set-z (nullp res 8))))

(defun psh (value set-fun b-w)
  (log-text "psh" value)
  (dec-reg 1)
  (set-mem (get-reg 1) value b-w))

(defun call (value set-fun)
  (log-text "call")
  ;(format t "~4,'0x" value)
  (psh (get-reg 0) nil 8)
  (set-reg 0 value))

(defun jump-decode (instn)
  (log-text "jump" instn)
  (print (get-reg 2) *log-stream*)
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
  ;(print offset)
  ;(print (ldb (byte 9 0) offset))
  ;(print (* (ldb (byte 1 9) offset) 1024))
  ;(print (- (* 2 (- (ldb (byte 9 0) offset)
;		    (* (ldb (byte 1 9) offset) 512)))))
  (set-reg 0 (+ (get-reg 0) 2
		(* 2 (- (ldb (byte 9 0) offset)
			(* (ldb (byte 1 9) offset) 512)))))
  t)

(defun double-decode (instn data1 data2)
  (log-text "double-op")
  (inc-reg 0)
  (let ((opcode (ldb (byte 4 12) instn))
	(source (ldb (byte 4 8) instn))
	(ad (ldb (byte 1 7) instn))
	(as (ldb (byte 2 4) instn))
	(dest (ldb (byte 4 0) instn))
	(b-w (if (= 1 (ldb (byte 1 6) instn))
		 0
		 8)))
    (multiple-value-bind (source-val source-fun ext-used)
	(address-decode as source data1 b-w)
      (multiple-value-bind (dest-val dest-fun)
	  (address-decode ad dest (if ext-used
				      data2    ;use the second extension word if
				      data1)   ;the first was used in the source
			  b-w)  
;      (let* ((source-lst (multiple-value-list (address-decode as source data1)))
;	     (source-val (car source-lst)))
;	;(print source-lst)
	;(log-text "source" source-val)
	;(format t "~4,'0x" source-val)
	;(log-text "dest" dest-val)
	;(format t "~4,'0x" dest-val)
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
  (log-text "mov" val)
 ;(format t "~4,'0x"  val)
;  (print dest-fun)
  (log-text "byte-word" b-w)
  (funcall dest-fun val b-w))

(defun add-flags (res b-w)
  (set-c (ldb (byte 1 (+ b-w 8)) res))
  (set-v 0)
  (set-n (negp res b-w))
  (set-z (nullp res b-w)))

(defun add (source-val dest-val dest-fun b-w)
  (log-text "add")
  (log-text "source" source-val)
 ;(format t "~4,'0x" source-val)
  (log-text "dest" dest-val)
 ;(format t "~4,'0x" dest-val)
  (log-text "byte-word" b-w)
  (let ((res (+ (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun addc (source-val dest-val dest-fun b-w)
  (log-text "addc")
  (let ((res (+ (trim-bw source-val b-w) (trim-bw dest-val b-w) (get-c))))
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun subc (source-val dest-val dest-fun b-w)
  (log-text "subc")
  (let ((res (+ (trim-bw dest-val b-w) (lognot (trim-bw source-val b-w)) (get-c) 1))) ;random +1 for bug compat
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun sub (source-val dest-val dest-fun b-w)
  (log-text "sub")
  (let ((res (+ (trim-bw dest-val b-w) (trim-bw (lognot source-val) b-w) 1)))
    (add-flags res b-w)
    (funcall dest-fun res b-w)))

(defun cmp (source-val dest-val b-w)
  (log-text "cmp" source-val dest-val)
  ;(format t "~4,'0x"  source-val)
  ;(format t "~4,'0x"  dest-val)
  (log-text "byte-word" b-w)
  (let ((res (+ (trim-bw dest-val b-w) (trim-bw (lognot source-val) b-w) 1)))
    (add-flags res b-w))
  (log-text "SR" (get-reg 2)))


(defun dadd (source-val dest-val dest-fun b-w)
  (log-text "dadd")
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
  (log-text "emu-bit")
  (let ((res (logand (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (set-v 0)
    (set-n (ldb (byte 1 (+ b-w 7)) res))
    (set-z (nullp res b-w))
    (set-c (nullp res b-w))))

(defun bic (source-val dest-val dest-fun b-w)
  (log-text "bic")
  (let ((res (logand (lognot (trim-bw source-val b-w)) (trim-bw dest-val b-w))))
    (funcall dest-fun res b-w)))

(defun bis (source-val dest-val dest-fun b-w)
  (log-text "bis")
  (funcall dest-fun (logior (trim-bw source-val b-w) (trim-bw dest-val b-w)) b-w))

(defun xor (source-val dest-val dest-fun b-w)
  (log-text "xor")
  (let ((res (logxor (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (funcall dest-fun res b-w)
    (set-v 0)
    (set-n (ldb (byte 1 (+ b-w 7)) res))
    (set-z (nullp res b-w))
    (set-c (nullp res b-w))))

(defun emu-and (source-val dest-val dest-fun b-w)
  (log-text "emu-and")
  (let ((res (logand (trim-bw source-val b-w) (trim-bw dest-val b-w))))
    (funcall dest-fun res b-w)
    (set-v 0)
    (set-n (ldb (byte 1 (+ b-w 7)) res))
    (set-z (nullp res b-w))
    (set-c (nullp res b-w))))

;start of file importing code
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
  (print "start of run")
  ;(setf *log-stream* *standard-output*)
  (setf *log-stream* (open "C:\\ben\\log.txt" :direction :output :if-exists :supersede :SHARING :external))
  (import-file file-name)
  (setf *input* input)
  (main)
  (print file-name)
  (print *console*)
  (print "error:")
  (print *err*)
  (print "unlocked?")
  (print *unlocked*))
