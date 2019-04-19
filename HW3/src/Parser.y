{
module Parser where

import Grammar
import Lexer
}

%name parseExpr
%tokentype { Token      }
%error     { parseError }
%monad     { Either String }{ >>= }{ return }

%token
    VARIABLE     { Variable $$  }
    IMPL         { ImplT        }
    OR           { OrT          }
    AND          { AndT         }
    NOT          { NotT         }
    LEFTBRACKET  { LeftBracket  }
    RIGHTBRACKET { RightBracket }

%%

Expr
  : Disj                            { $1                }
  | Disj IMPL Expr                  { Binary Impl $1 $3 }

Disj
  : Conj                            { $1                }
  | Disj OR Conj                    { Binary Or $1 $3   }

Conj
  : Negate                          { $1                }
  | Conj AND Negate                 { Binary And $1 $3  }

Negate
  : NOT Negate                      { Not $2            }
  | VARIABLE                        { Var $1            }
  | LEFTBRACKET Expr RIGHTBRACKET   { $2                }

{
parseError = fail "Parse error"
}





