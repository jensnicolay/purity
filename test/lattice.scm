(let ((_lexico5 (lambda (_base6) (let ((_lex-fixed7 (lambda (_fixed8 _lhs9 _rhs10) (let ((_check11 '<undefined>)) (let ((_$103 (set! _check11 (lambda (_lhs12 _rhs13) (let ((_p97 (null? _lhs12))) (if _p97 _fixed8 (let ((_p98 (car _lhs12))) (let ((_p99 (car _rhs13))) (let ((_probe14 (_base6 _p98 _p99))) (let ((__t015 (eq? _probe14 'equal))) (let ((_p100 (if __t015 __t015 (eq? _probe14 _fixed8)))) (if _p100 (let ((_p101 (cdr _lhs12))) (let ((_p102 (cdr _rhs13))) (_check11 _p101 _p102))) 'uncomparable)))))))))))) (_check11 _lhs9 _rhs10)))))) (let ((_lex-first16 '<undefined>)) (let ((_$114 (set! _lex-first16 (lambda (_lhs17 _rhs18) (let ((_p104 (null? _lhs17))) (if _p104 'equal (let ((_p105 (car _lhs17))) (let ((_p106 (car _rhs18))) (let ((_probe19 (_base6 _p105 _p106))) (let ((__t120 _probe19)) (let ((_p107 (memv __t120 '(less more)))) (if _p107 (let ((_p108 (cdr _lhs17))) (let ((_p109 (cdr _rhs18))) (_lex-fixed7 _probe19 _p108 _p109))) (let ((_p110 (memv __t120 '(equal)))) (if _p110 (let ((_p111 (cdr _lhs17))) (let ((_p112 (cdr _rhs18))) (_lex-first16 _p111 _p112))) (let ((_p113 (memv __t120 '(uncomparable)))) (if _p113 'uncomparable '<undefined>)))))))))))))))) _lex-first16)))))) (let ((_make-lattice21 (lambda (_elem-list22 _cmp-func23) (cons _elem-list22 _cmp-func23)))) (let ((_lattice->elements24 car)) (let ((_lattice->cmp25 cdr)) (let ((_rotate27 '<undefined>)) (let ((_$117 (set! _rotate27 (lambda (_fo28 _fum29) (let ((_next30 (cdr _fo28))) (let ((_$115 (set-cdr! _fo28 _fum29))) (let ((_p116 (null? _next30))) (if _p116 _fo28 (_rotate27 _next30 _fo28))))))))) (let ((_reverse!26 (lambda (_lst31) (let ((_p118 (null? _lst31))) (if _p118 '() (_rotate27 _lst31 '())))))) (let ((_zulu-select32 (lambda (_test33 _lst34) (let ((_select-a35 '<undefined>)) (let ((_$123 (set! _select-a35 (lambda (_ac36 _lst37) (let ((_p119 (null? _lst37))) (if _p119 (_reverse!26 _ac36) (let ((_head38 (car _lst37))) (let ((_p120 (_test33 _head38))) (let ((_p121 (if _p120 (cons _head38 _ac36) _ac36))) (let ((_p122 (cdr _lst37))) (_select-a35 _p121 _p122))))))))))) (_select-a35 '() _lst34)))))) (let ((_select-map39 (lambda (_test40 _func41 _lst42) (let ((_select-a43 '<undefined>)) (let ((_$129 (set! _select-a43 (lambda (_ac44 _lst45) (let ((_p124 (null? _lst45))) (if _p124 (_reverse!26 _ac44) (let ((_head46 (car _lst45))) (let ((_p125 (_test40 _head46))) (let ((_p127 (if _p125 (let ((_p126 (_func41 _head46))) (cons _p126 _ac44)) _ac44))) (let ((_p128 (cdr _lst45))) (_select-a43 _p127 _p128))))))))))) (_select-a43 '() _lst42)))))) (let ((_map-and47 (lambda (_proc48 _lst49) (let ((_p130 (null? _lst49))) (if _p130 #t (let ((_drudge50 '<undefined>)) (let ((_$135 (set! _drudge50 (lambda (_lst51) (let ((_rest52 (cdr _lst51))) (let ((_p131 (null? _rest52))) (if _p131 (let ((_p132 (car _lst51))) (_proc48 _p132)) (let ((_p133 (car _lst51))) (let ((_p134 (_proc48 _p133))) (if _p134 (_drudge50 _rest52) #f)))))))))) (_drudge50 _lst49)))))))) (let ((_maps-153 (lambda (_source54 _target55 _pas56 _new57) (let ((_scmp58 (_lattice->cmp25 _source54))) (let ((_tcmp59 (_lattice->cmp25 _target55))) (let ((_less60 (_select-map39 (lambda (_p61) (let ((_p136 (car _p61))) (let ((_p137 (_scmp58 _p136 _new57))) (eq? 'less _p137)))) cdr _pas56))) (let ((_more62 (_select-map39 (lambda (_p63) (let ((_p138 (car _p63))) (let ((_p139 (_scmp58 _p138 _new57))) (eq? 'more _p139)))) cdr _pas56))) (let ((_p143 (_lattice->elements24 _target55))) (_zulu-select32 (lambda (_t64) (let ((_p141 (_map-and47 (lambda (_t265) (let ((_p140 (_tcmp59 _t265 _t64))) (memq _p140 '(less equal)))) _less60))) (if _p141 (_map-and47 (lambda (_t266) (let ((_p142 (_tcmp59 _t266 _t64))) (memq _p142 '(more equal)))) _more62) #f))) _p143))))))))) (let ((_maps-rest67 '<undefined>)) (let ((_$149 (set! _maps-rest67 (lambda (_source68 _target69 _pas70 _rest71 _to-172 _to-collect73) (let ((_p144 (null? _rest71))) (if _p144 (_to-172 _pas70) (let ((_next74 (car _rest71))) (let ((_rest75 (cdr _rest71))) (let ((_p147 (_maps-153 _source68 _target69 _pas70 _next74))) (let ((_p148 (map (lambda (_x76) (let ((_p145 (cons _next74 _x76))) (let ((_p146 (cons _p145 _pas70))) (_maps-rest67 _source68 _target69 _p146 _rest75 _to-172 _to-collect73)))) _p147))) (_to-collect73 _p148))))))))))) (let ((_maps77 (lambda (_source78 _target79) (let ((_p150 (_lattice->elements24 _source78))) (let ((_p152 (_maps-rest67 _source78 _target79 '() _p150 (lambda (_x80) (let ((_p151 (map cdr _x80))) (cons _p151 '()))) (lambda (_x81) (apply append _x81))))) (let ((_p153 (_lattice->cmp25 _target79))) (let ((_p154 (_lexico5 _p153))) (_make-lattice21 _p152 _p154)))))))) (let ((_sum82 '<undefined>)) (let ((_$159 (set! _sum82 (lambda (_lst83) (let ((_p155 (null? _lst83))) (if _p155 0 (let ((_p156 (car _lst83))) (let ((_p157 (cdr _lst83))) (let ((_p158 (_sum82 _p157))) (+ _p156 _p158)))))))))) (let ((_count-maps84 (lambda (_source85 _target86) (let ((_p160 (_lattice->elements24 _source85))) (_maps-rest67 _source85 _target86 '() _p160 (lambda (_x87) 1) _sum82))))) (let ((_run88 (lambda () (let ((_l289 (_make-lattice21 '(low high) (lambda (_lhs90 _rhs91) (let ((__t292 _lhs90)) (let ((_p161 (memv __t292 '(low)))) (if _p161 (let ((__t393 _rhs91)) (let ((_p162 (memv __t393 '(low)))) (if _p162 'equal (let ((_p163 (memv __t393 '(high)))) (if _p163 'less (display 'make-lattice "base" _rhs91)))))) (let ((_p164 (memv __t292 '(high)))) (if _p164 (let ((__t494 _rhs91)) (let ((_p165 (memv __t494 '(low)))) (if _p165 'more (let ((_p166 (memv __t494 '(high)))) (if _p166 'equal (display 'make-lattice "base" _rhs91)))))) (display 'make-lattice "base" _lhs90)))))))))) (let ((_l395 (_maps77 _l289 _l289))) (let ((_l496 (_maps77 _l395 _l395))) (let ((_$167 (_count-maps84 _l289 _l289))) (let ((_$168 (_count-maps84 _l395 _l395))) (let ((_$169 (_count-maps84 _l289 _l395))) (let ((_$170 (_count-maps84 _l395 _l289))) (_count-maps84 _l496 _l496))))))))))) (_run88)))))))))))))))))))