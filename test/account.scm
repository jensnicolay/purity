(let ((message-withdraw 0)) (let ((message-deposit 1)) (letrec ((make-account (lambda (balance) (letrec ((withdraw (lambda (amount) (let ((_68 (>= balance amount))) (if _68 (let ((_69 (let ((_71 (- balance amount))) (let ((_70 _71)) (set! balance _70))))) balance) -1))))) (letrec ((deposit (lambda (amount) (let ((_72 (let ((_74 (+ balance amount))) (let ((_73 _74)) (set! balance _73))))) balance)))) (letrec ((dispatch (lambda (m) (let ((_75 (= m message-withdraw))) (if _75 withdraw (let ((_76 (= m message-deposit))) (if _76 deposit -2))))))) dispatch)))))) (let ((_77 (make-account 100))) (let ((account _77)) (let ((_78 (let ((_90 (account message-withdraw))) (let ((_79 _90)) (let ((_91 (_79 50))) (let ((_80 _91)) _80)))))) (let ((_81 (let ((_92 (account message-withdraw))) (let ((_82 _92)) (let ((_93 (_82 60))) (let ((_83 _93)) _83)))))) (let ((_84 (let ((_94 (account message-deposit))) (let ((_85 _94)) (let ((_95 (_85 40))) (let ((_86 _95)) _86)))))) (let ((_87 (let ((_96 (account message-withdraw))) (let ((_88 _96)) (let ((_97 (_88 60))) (let ((_89 _97)) _89)))))) 30)))))))))
