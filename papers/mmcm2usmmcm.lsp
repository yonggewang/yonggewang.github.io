;                             TR.LSP
;                          Wang Yong-ge
;                Nankai Institute of Mathematics
;                   Nankai University,Tian Jin
;                      30071,P.R.China
;
;This is the program to translate the US MMCM into a parallel computation
;              Part 1: Input the Productions
(dos "cls")
(setf p "Welcome you to use this software!")
(print p)
(setf ppp " Beginning? ")
(setf ttt (read-line))
(setf *print-length* nil)
(setf *print-level* nil)
(dos "cls")
(setf p30 "   where is the data? ")
(setf p31 "   1.productions are on disk. ")
(setf p32 "   2.productions will be inputed from keyboard. ")
(setf p33 "Qin xuan ze:---")
(print p30)
(print p31)
(print p32)
(print p33)
(setf FSH (read))
(cond ((= FSH 2)
   (setf p1 "Please input the number of Productions in all: ")
   (setq N (read))
   (setq NN (+ N N))
   (defstruct production
     (premise nil)
     (poperating nil)
     (pstate nil)
     (result nil)
     (roperating nil)
     (rnewborn nil)
     (rstate nil))
   (setf proarray (make-array NN))
   (do ((NNN 0 (1+ NNN)))
       ((= NNN NN) (terpri))
       (setf (aref proarray NNN) (make-production)))
   (setf p40 "please input the halting state: ")
   (setf p3 "Now it's the time to input the productions ")
   (setf p4 "And here is an example of how to input the productions ")
   (setf p5 '((a 1) (v 1) (a 3) (v 2) (a 5)))
   (setf p6 '(1 3 5))
   (setf p7 '((b 1) (b 2) (b 3) (b 4) (b 5) (b 6)))
   (setf p8 '((2 0) (4 0) (6 0)))
   (setf p9 '(2 3))
   (setf p35 'q0)
   (terpri)
   (print p3)
   (print p4)
   (terpri)
   (print p5)
   (print p6)
   (print p7)
   (print p8)
   (print p9)
   (print p35)
   (do ((I 0 (1+ I)))
      ((= I N)(terpri))
      (setf p10 "Please input the premise of production ")
      (setf p11 "please input the operating words of this production ")
      (setf p50 "please input the pstate of this production")
      (setf p12 "please input the result words of this production ")
      (setf p13 "please input the newoperating words of this production ")
      (setf p14 "please input the newborn words of this production ")
      (setf p15 "like this: ")
      (setf p36 "please input the rstate words")
      (print p10)
      (prin1 (1+ I))
      (print p15)
      (print p5)
      (terpri)
      (setf (aref proarray I)(make-production))
      (setf (production-premise (aref proarray I))(read))
      (print p11)
      (print p15)
      (print p6)
      (terpri)
      (setf (production-poperating (aref proarray I))(read))
      (print p50)
      (print p15)
      (print p35)
      (terpri)
      (setf (production-pstate (aref proarray I))(read-line))
      (print p12)
      (print p15)
      (print p7)
      (terpri)
      (setf (production-result (aref proarray I))(read))
      (print p13)
      (print p15)
      (print p8)
      (terpri)
      (setf (production-roperating (aref proarray I))(read))

      (print p14)

      (print p15)

      (print p9)

      (terpri)

      (setf (production-rnewborn (aref proarray I))(read))

      (print p36)

      (print p15)

      (print p35)

      (terpri)

      (setf (production-rstate (aref proarray I))(read-line)))

   (setf p15 "you have finished the work of inputing productions!")

   (print p15)

   (setf p16 "Now please input the first condition,i.e. the length")

   (setf p17 "of the initial word and the position of operating letters")

   (print p16)

   (print p17)

   (setf p18 "the length is: ")

   (print p18)

   (setf M (read))

   (setf p19 "the position of operating letters is: ")

   (print p19)

   (setf o (read))

   (setf operating o)

   (setf qh "qe")

   (setf p20 "Now I'm working, please waiting... ... "))

      ((= FSH 1)

   (setf p16 "Now please input the first condition,i.e. the length")

   (setf p20 "Now I'm working, please waiting... ... ")

   (setf p17 "of the initial word and the position of operating letters")

   (setf p18 "the length is: ")

   (setf p19 "the position of operating words is: ")

   (setf p40 "please input the halting state: ")

   (setf p34 "please input the path and filename of productions:")

   (defun rd1(W)

          (setf stream8 (open W :direction :input)))

   (print p34)

   (setf fname (read-line))

   (rd1 fname)

   (setf tt 'T)

   (do ((Z 0 (1+ Z)))

     ((not tt)(terpri))

     (setf N Z)

     (setf tt (read stream8)))

   (close stream8)

   (defun rd(W)

          (setf stream9 (open W)))

   (rd fname)

   (defstruct production

     (premise nil)

     (poperating nil)

     (pstate nil)

     (result nil)

     (roperating nil)

     (rnewborn nil)

     (rstate nil))

   (setf NN (+ N N))

   (setf proarray (make-array NN))

   (do ((NNN 0 (1+ NNN)))

       ((= NNN NN)(terpri))

       (setf (aref proarray NNN) (make-production)))

   (setf protion 'T)

   (do ((U 0 (1+ U)))

       ((not protion)(terpri))

       (setf protion (read stream9))

       (setf (production-premise (aref proarray U)) (car protion))

       (setf (production-poperating (aref proarray U)) (cadr protion))

       (setf (production-pstate (aref proarray U)) (caddr protion))

       (setf (production-result (aref proarray U)) (car (cdddr protion)))

       (setf (production-roperating (aref proarray U)) (cadr (cdddr protion)))

       (setf (production-rnewborn (aref proarray U)) (car (cddr (cdddr protion))))

       (setf (production-rstate (aref proarray U)) (cadr (cddr (cdddr protion)))))

   (close stream9)

   (print p16)

   (print p17)

   (print p18)

   (setf M (read))

   (print p19)

   (setf o (read))

   (setf qh "qe")

   (setf operating o)))

   (print p20)

;the input work has been finished,the length of initial words is M, the

;number of production is N and the productions are in array proarray.

;

;           Part 2: the classification

;

;    the function of making the resulting word adapted to production.

;

(defun adapt(leng word opting)         ;leng is the length of word

       (setf chang (length opting))    ;chang is the length of operating words

       (setf biao0 nil)   ;word

       (setf biao1 nil)   ;operating

       (setf azhi (make-array (1+ chang)))

       (do ((aii 0 (1+ aii)))

           ((= aii chang)(terpri))

           (setf ace (nth aii opting))

           (setf acezhi (nth (- ace 1) word))

           (setf (aref azhi (1+ aii)) acezhi))

       (setf ot opting)

       (setf ot (append (list 0) ot))

       (setf xx (list (1+ leng )))

       (setf ot (append ot xx))

       (setf ophao 1)        ;operating new position

       (setf vhao 1)         ;v's position

       (setf vzhi (make-array (+ 3 chang)))

       (do ((bian 0 (1+ bian)))      ;bian is the bian liang

           ((= bian (1+ chang)) (terpri))

           (setf A1 (NTH bian ot))

           (setf A2 (NTH (1+ bian) ot))

           (cond ((= A1 (nth (- chang 1) opting))

                  (cond ((= A2 (1+ A1))

                         (terpri))

                        ((/= A2 (1+ A1))

                         (setf fir (subseq word A1))

                         (setf www (list 'v))

                         (setf TJ (append www  (list vhao)))

                         (setf (aref vzhi vhao) fir)

                         (setf biao0 (append biao0 (list TJ))))))

                 ((= A2 (1+ A1))

                  (setf fir (nth (- A2 1) word))

                  (setf biao0 (append biao0 (list fir)))

                  (setf biao1 (append biao1 (list ophao)))

                  (setf ophao (1+ ophao)))

                 ((/= A2 (1+ A1))

                  (setf sec (nth (- A2 1) word))

                  (setf fir (subseq word A1 (- A2 1)))

                  (setf TTT vhao)          ;v's position

                  (setf TJ (append (list 'v) (list TTT)))

                  (setf (aref vzhi TTT) fir);v(x) is stored in the (x+1)th

                  (setf biao0 (append biao0 (list TJ)))   ;room of vzhi array

                  (setf biao0 (append biao0 (list sec)))

                  (setf ophao (1+ ophao))

                  (setf biao1 (append biao1 (list ophao)))

                  (setf ophao (1+ ophao))

                  (setf vhao (1+ vhao))))))

;when adapt function finished,biao0 is the word and biao1 is the operating

;v's original value is in vizhi.

;

;        the function of searching for proper production

(defun search(premise1 operating1 state1)

(prog( )

     (setf J 0)

 loop

     (cond((< J N)(cond((not(and(= (length (production-premise(aref proarray J)))

                                     (length premise1))

                               (equal(production-pstate (aref proarray J))

                                    state1)

                               (equal(production-poperating (aref proarray J))

                                     operating1)))

                        (setf J (1+ J)) (go loop))

                      ((and (= (length (production-premise (aref proarray J)))

                                  (length premise1))

                            (equal (production-pstate (aref proarray J))

                                   state1)

                            (equal (production-poperating (aref proarray J))

                                   operating1))

                        (setf pr J) (return pr))))

           ((= J N) (setf jieshu 'T) (setf pr J) (return jieshu)))))

;when search ended,the proper production is in pr'th of proarray.

;

;            the huan yuan function

;

(defun huanyuan (X V Y Z S I);X is the array of v's value

                             ;V is the array of a's value

                             ;Y is the old word

                             ;Z is the operating

                             ;S is the newborn words

                             ;I means the Ith process

       (setf outA nil)   ; word

       (setf outB nil)   ; operating

       (setf outC nil)   ; newborn words

       ;

       ; the subprogram of getting the newborn words

       ;

          (cond ((not (null S))

           (setf oxuhao (car S))

           (setf ooutA nil)

           (setf ozibiao (subseq Y 0 (- oxuhao 1)))

           (setf ozichang (length ozibiao))

           (do ((oqq 0 (1+ oqq)))

               ((= oqq ozichang)(terpri))

                (setf oceshi (nth oqq ozibiao))

                (cond ((string= (symbol-name (car oceshi)) "V")

                       (setf oqqq (nth 1 oceshi))

                       (setf oapp (aref X oqqq))

                       (setf ooutA (append ooutA oapp)))

                      ((not(string= (symbol-name (car oceshi)) "V"))

                       (setf ooutA (append ooutA (list oceshi))))))

           (setf ocishi (length S))

           (setf oS (append S (list (1+ (length Y)))))

           (setf ooS oS)

           (do ((oqq 0 (1+ oqq)))

               ((= oqq ocishi)(terpri))

                (setf ooutA (append ooutA (list (nth (- (car ooS) 1) Y))))

                (setf ooS (cdr ooS))

                (setf outC (append outC (list (length ooutA))))

               (setf obetw1 oqq)

               (setf obetw2 (1+ oqq))

               (setf obetwnumf (nth obetw1 oS))

               (setf obetwnuml (nth obetw2 oS))

               (do ((obianliang obetwnumf (1+ obianliang)))

                   ((= obianliang (- obetwnuml 1))(terpri))

                    (setf oyuansu (nth obianliang Y))

                    (cond ((string= (symbol-name (car oyuansu)) "V")

                           (setf oqqq (nth 1 oyuansu))

                           (setf oapp (aref X oqqq))

                           (setf ooutA (append ooutA oapp)))

                          ((not(string= (symbol-name (car oyuansu)) "V"))

                           (setf ooutA (append ooutA (list oyuansu))))))))

          ((null S) (setf outC nil)))

       ;end of subprogram getting newborn words

       ;

     (cond ((not (null Z))

       (setf xuhao (nth 0 (car Z)))

       (setf zibiao (subseq Y 0 (- xuhao 1)))

       (setf zichang (length zibiao))

       (do ((qq 0 (1+ qq)))

           ((= qq zichang)(terpri))

            (setf ceshi (nth qq zibiao))

            (cond ((string= (symbol-name (car ceshi)) "V")

                   (setf qqq (nth 1 ceshi))

                   (setf app (aref X qqq))

                   (setf outA (append outA app)))

                  ((not(string= (symbol-name (car ceshi)) "V"))

                   (cond ((string= (symbol-name (car ceshi)) "A")

                          (setf aqqq (nth 1 ceshi))

                          (setf aapp (aref V aqqq))

                          (setf outA (append outA (list aapp))))

                         ((not (string= (symbol-name (car ceshi)) "A"))

                          (setf outA (append outA (list ceshi))))))))

       (setf cishu (length Z))

       (setf zzzzz (append (list (1+ (length Y))) (list 0)))

       (setf Z (append Z (list zzzzz)))

       (setf Z1 Z)

       (do ((qq 0 (1+ qq)))

           ((= qq cishu)(terpri))

            (cond ((= 0 (nth 1 (car Z)))

                   (setf apphao (caar Z))     ;If it's 0, then it is surely

                   (setf app (subseq Y (- apphao 1) apphao)) ; not v's

                   (setf Z (cdr Z))

                   (cond ((string= (symbol-name (caar app)) "A")

                          (setf aqqq (nth 1 (car app)))

                          (setf app (aref V aqqq))

                          (setf outA (append outA (list app))))

                         ((not (string= (symbol-name (caar app)) "A"))

                          (setf outA (append outA app))))

                   (setf outB (append outB (list (length outA)))))

                  ((= 1 (nth 1 (car Z)))

                   (setf v-hao (cadr (nth (- (caar Z) 1) Y)))

                   (setf fanhui (aref X v-hao))

                   (setf bchang (length outA))

                   (setf Z (cdr Z))

                   (setf outA (append outA fanhui))

                   (setf outB (append outB (list (1+ bchang)))))

                  ((= 2 (nth 1 (car Z)))

                   (setf v-hao (cadr (nth (- (caar Z) 1) Y)))

                   (setf fanhui (aref X v-hao))

                   (setf Z (cdr Z))

                   (setf outA (append outA fanhui))

                   (setf bchang (length outA))

                   (setf outB (append outB (list bchang))))

                  ((= 3 (nth 1 (car Z)))

                   (setf v-hao (cadr (nth (- (caar Z) 1) Y)))

                   (setf fanhui (aref X v-hao))

                   (setf Z (cdr Z))

                   (setf bchang (length outA))

                   (setf outB (append outB (1+ bchang)))

                   (setf outA (append outA fanhui))

                   (setf bchang (length outA))

                   (setf outB (append outB (list bchang)))))

            (setf betw1 qq)               ;deal with words between operating

            (setf betw2 (1+ qq))

            (setf betwnumf (car (nth betw1 Z1)))

            (setf betwnuml (car (nth betw2 Z1)))

            (do ((bianliang betwnumf (1+ bianliang)))

                ((= bianliang (- betwnuml 1))(terpri))

                (setf yuansu (nth bianliang Y))

                (cond ((string= (symbol-name (car yuansu)) "V")

                       (setf qqq (nth 1 yuansu))

                       (setf app (aref X qqq))

                       (setf outA (append outA app)))

                      ((not(string= (symbol-name (car yuansu)) "V"))

                       (cond ((string= (symbol-name (car yuansu)) "A")

                              (setf aqqq (nth 1 yuansu))

                              (setf aapp (aref V aqqq))

                              (setf outA (append outA (list aapp))))

                             ((not (string= (symbol-name (car yuansu)) "A"))

                              (setf outA (append outA (list yuansu))))))))))

          ((null Z)

           (do ((qq 0 (1+ qq)))

               ((= qq (length Y))(terpri))

               (setf ceshi (nth qq Y))

               (cond ((string= (symbol-name (car ceshi)) "V")

                      (setf qqq (nth 1 ceshi))

                      (setf app (aref X qqq))

                      (setf outA (append outA app)))

                     ((not (string= (symbol-name (car ceshi)) "V"))

                      (cond ((string= (symbol-name (car ceshi)) "A")

                             (setf aqqq (nth 1 ceshi))

                             (setf aapp (aref V aqqq))

                             (setf outA (append outA (list aapp))))

                            ((not (string= (symbol-name (car ceshi)) "A"))

                             (setf outA (append outA (list ceshi))))))))

               (setf outB nil)))

       ;to marke the newborn words

       (setf markl (length outC))

       (setf otc outC)

       (do ((markI 0 (1+ markI)))

            ((= markI (length outC))(terpri))

            (setf mk (car otc))

            (setf otc (cdr otc))

            (setf tihuan (nth (- mk 1) outA))

            (setf tihuan (append tihuan (list I)))

            (setf (nth (- mk 1) outA) tihuan)))

           ;the end of marking

;   the end of huanyuan function

;

;

;        the function of getting the process of computation

;

(defun getprocess(filename)

      (setf stream1 (open filename :direction :output))

      (setf K 0)                         ;to set the first condition

      (setf process0 K)

      (setf process1 nil)

      (do ((S 0 (1+ S)))

        ((= S M)(terpri))

        (setf wwww (list 'a))

        (setf process1 (append process1 (list (append wwww (list (1+ S)))))))

      (setf pso (list process0 process1))

      (setf pso (append pso (list operating) (list "q0")))   ;the first word is like:

      (print pso stream1)           ;(bu ((a 1) (a 2) (a 3) ... (a m))(1 3 5) "q0")

      ;   begin to simulating the serial computation

      (setf jieshu nil)

      (setf A (cadr pso))    ;A is the premise

      (setf B operating)     ;B is the operating

      (setf D "q0")

      (do ((YY 0 (1+ YY)))

          ((not (null jieshu))(terpri))

          (setf C (length A))

          (adapt C A B)

          (search biao0 biao1 D)

          (cond ((not jieshu)

                 (setf A (production-result (aref proarray pr)))

                 (setf B (production-roperating (aref proarray pr)))

                 (setf C (production-rnewborn (aref proarray pr)))

                 (setf D (production-rstate (aref proarray pr)))))

          (setf Y0 (1+  YY))

          (huanyuan vzhi azhi A B C Y0)

          (setf A outA)

          (setf B outB)

          (setf pso (list Y0 outA outB outC D))

          (cond ((string= D qh)

                 (setf jieshu 'T)))

          (print pso stream1))

      (print nil stream1)

      (close stream1))

; end of getting process function

;

;

;     the function of getting the number of elements in one

;                file and setting the elements in one array

;

(defun getnumber(file)

       (setf stream (open file))

       (setf fce 'T)

       (do ((fi 0 (1+ fi)))

            ((null fce)(terpri))

            (setf fce (read stream))

            (setf number fi))

       (close stream)

       (setf streamf (open file))

       (setf filearray (make-array number))

       (do ((fii 0 (1+ fii)))

           ((= fii number)(terpri))

           (setf (aref filearray fii) (read streamf)))

       (close streamf))

;   end of getting number

;

;

; the function of getting the maximum of two numbers

(defun mum(x1 x2)

      (cond ((> x1 x2)

             (setf mu x1))

            ((< x1 x2)

             (setf mu x2))

            ((= x1 x2)

             (setf mu x1))))

;end of maximum function

;

;

;    the function of getting the level of operating words

;

(defun getlevel(filename1 filename2)

      (getnumber filename1)

      (setf stream2 (open filename1))

      (setf stream3 (open filename2 :direction :output))

      (setf level 0)

      (print (list 1 0) stream3)

      (read stream2)

      (do ((ji 0 (1+ ji)))

          ((= ji (- number 2))(terpri))

           (setf cao (read stream2))

           (setf lamda (car (cddr cao)))

           (setf wordof (cadr cao))

           (setf lamdalen (length lamda))

           (setf llevel 0)

           (cond ((not (null lamda))

                  (setf aa1 (caddr (nth (- (car lamda) 1) wordof)))

                  (setf lamda (cdr lamda))

                  (cond ((null aa1) (setf aa11 0))

                         (T (setf aa11 aa1)))

                  (do ((jil 1 (1+ jil)))

                      ((null lamda)(terpri))

                      (setf aa2 (caddr (nth (- (car lamda) 1) wordof)))

                      (setf lamda (cdr lamda))

                      (cond ((null aa2)(setf aa22 0))

                             (T (setf aa22 aa2)))

                      (mum aa11 aa22)

                      (setf aa11 mu))

                   (setf level aa11)

                   (mum llevel level)

                   (setf llevel mu)

                   (setf plevel (list (+ 2 ji) llevel))

                   (print plevel stream3))

                 ((null lamda)

                  (setf plevel (list (+ 2 ji) (1+ llevel)))

                  (print plevel stream3))))

      (print nil stream3)

      (close stream2)

      (close stream3))

      ; the file level.txt storing the (bu level),where at the level

      ;step the operating words is generated

;   end of getting level function

;

;

;       the function of getting k's

;

(defun getks(filename1 filename2)

      (getnumber filename1)

      (setf stream20 (open filename1))

      (setf kice 'T)

      (setf klevel (make-array number))

      (do ((kii 0 (1+ kii)))

          ((= kii number)(terpri))

          (setf (aref klevel kii) nil))

      (setf kchang 1)

      (setf kice (read stream20))

      (setf (aref klevel 0) (list (car kice)))

      (do ((kib 0 (1+ kib)))

          ((not kice)(terpri))

          (setf kip kib)

          lp

          (setf kice (read stream20))

          (cond ((not(null kice))

                 (cond ((= (car kice) (1+ (cadr kice)))

                        (setf tianjia (append (aref klevel kib) (list (car kice))))

                        (setf (aref klevel kib) tianjia)

                        (setf kip (1+ kip))

                        (go lp))

                       ((/= (car kice) (1+ (cadr kice)))

                        (setf kchang (1+ kchang))

                        (setf tianjia (append (aref klevel (1+ kib)) (list (car kice))))

                        (setf (aref klevel (1+ kib)) tianjia))))

                ((null kice)(terpri))))

      (close stream20)

      ;in the array klevel stored the (3 4 5),which is a PSCPP.

      ;print k1,k2,...,km to file "A:klevel.txt"

      (setf stream21 (open filename2 :direction :output))

      (setf knumber number)

      (do ((ki 0 (1+ ki)))

          ((= ki kchang)(terpri))

          (setf pk (aref klevel ki))

          (print pk stream21))

      (print nil stream21)

      (close stream21))

      ;the k(i)'s have been got

;end of getting k's

;

;

;

;   the function of getting the maximum parallel in the computation

;   i.e. of getting the I1,I2,I3,...,Il.

(defun getIs(filename1 filename2)

      (getnumber filename1)

      (setf pklevel (make-array kchang))

      (setf (aref pklevel 0) 0)

      (setf pkchang 1)

      (do ((pki 1 (1+ pki)))

          ((= pki knumber)(terpri))

          (setf k (aref klevel pki))

          (setf ooo (length k))

          (setf thisbu 0)

          (do ((ppp 0 (1+ ppp)))

              ((= ppp ooo)(terpri))

              (setf kce (car k))

              (setf kce (aref filearray (- kce 1)))

              (setf kce (nth 1 kce))

              (setf k (cdr k))

              (prog( )

                (do ((sss 0 (1+ sss)))

                    ((= sss pki)(terpri))

                    (setf ssss (aref klevel sss))

                    (cond ((member kce ssss)

                           (setf kcebu (1+ (aref pklevel sss)))

                           (mum kcebu thisbu)

                           (setf thisbu mu)

                           (return thisbu))))))

         (setf pkchang (1+ pkchang))

         (setf (aref pklevel pki) thisbu))

      ;get the k's classification,i.e.the I's

      (setf stream30  (open filename2 :direction :output))

      (setf Ilevel (make-array kchang))

      (do((ib 0 (1+ ib)))

         ((= ib kchang)(terpri))

         (setf (aref Ilevel ib) nil))

      (do((ik 0 (1+ ik)))

         ((= ik kchang)(terpri))

         (setf ice (aref pklevel ik))

         (setf iapp (append (aref ilevel ice) (list (1+ ik))))

         (setf (aref ilevel ice) iapp))

      ;print it to file

      (setf ppi 'T)

      (do ((ib 0 (1+ ib)))

          ((null ppi)(terpri))

          (setf ppi (aref Ilevel ib))

          (print ppi stream30))

      (print nil stream30)

      (close stream30))

      ;We have got the Ilevel.txt,in this file store the (1 2 3) meaning

      ;that k1 k2 k3 can be implemented parallely

;

;

;    GET THE COMPUTATION PROCESS

;

(dos "cls")

(setf profile (string-append  fname ".pro"))

(getprocess profile)

(setf levelfile (string-append fname ".lev"))

(getlevel profile levelfile)

(setf ksfile (string-append fname ".ks"))

(getks levelfile ksfile)

(setf Isfile (string-append fname ".Is"))

(getIs levelfile Isfile)

;

;

;    END OF COMPUTATION PROCESS

;

;

;    To print the result on the screen.

;

(dos "cls")

(setf p21 "I have finished the translation!")

(setf p22 "          If you want to copy this result to the printer, please

          return to the DOS system and just type the file:name.pro,name.ks

          and name.Is on user's disk:.where ks refers to k1,k2,...and is

          refers to I1,I2,I3,...")

(setf p23 "this is the serial computation process: ")

(setf p25 "please strike any key and RETURN to go on......")

(print p21)

(print p25)

(read-line)

(setf p26 'T)

(print p23)

(defun  pri1(qq)

    (setf stream6 (open qq)))

(pri1 profile)

(do ((I 0 (1+ I)))

    ((null p26)(terpri))

    (setf p26 (read stream6))

    (print p26))

(close stream6)

(dos "cls")

(print p25)

(read-line)

(setf p24 "this is the k's,i.e.the Pure Serial Computation 

           Partial Process(PSCPP)")

(print p24)

(setf p27 'T)

(defun pri2(qq)

      (setf stream7 (open qq)))

(pri2 ksfile)

(do((I 0 (1+ I)))

   ((null p27)(terpri))

   (setf p27 (read stream7))

   (print p27))

(close stream7)

(dos "cls")

(print p25)

(read-line)

(setf p50 "this is the I's,i.e.the classification for simulating sequential

           computation with the parallel implementation in I's")

(setf p51 'T)

(print p50)

(defun pri3(qq)

      (setf stream50 (open qq)))

(pri3 Isfile)

(do((I 0 (1+ I)))

   ((null p51)(terpri))

   (setf p51 (read stream50))

   (print p51))

(close stream50)

(print p22)

(setf p28 "Thank you for use this software!")

(setf p29 "Good-by!")

(dos "cls")

(print p28)

(print p29)









