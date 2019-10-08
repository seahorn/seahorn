;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

(
 (c++-mode (c-basic-offset . 2))
 (c-mode . ((c-basic-offset . 2)))
 (nil . ((eval . (add-to-list 'auto-mode-alist '("\\.h\\'" . c++-mode)))
         (eval . (if (boundp 'c-offsets-alist)
                     (add-to-list 'c-offsets-alist '(innamespace . -))))
         (eval . (setq lsp-file-watch-threshold nil))
         ))
 )
