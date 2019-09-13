{
module Lexer where
}

%wrapper "basic"

$digit     = 0-9
$alpha     = [A-Za-z]
$apostrophe = '

tokens :-

    $white+                                 ;
    &                                       { \_ -> AndT          }
    \|                                      { \_ -> OrT           }
    "->"                                    { \_ -> ImplT         }
    !                                       { \_ -> NotT          }
    \(                                      { \_ -> LeftBracket   }
    \)                                      { \_ -> RightBracket  }
    $alpha [$alpha $digit $apostrophe]*     { \s -> Variable s    }


{

data Token = AndT
           | OrT
           | ImplT
           | NotT
           | LeftBracket
           | RightBracket
           | Variable String
           deriving (Show, Eq)
}
