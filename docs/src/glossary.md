unit fraction
    A fraction with a numerator of 1. For example, 1/2, 1/3, and 1/4 are unit fractions.
    [ "The Rational Number n/p  as a sum of two unit fractions"
      Konstantine Zelator, 2012-Feb-29. https://arxiv.org/pdf/1203.0018
    ]      ]

unit fraction and complementary unit fraction
    A unit fraction is a positive rational number 1/K with numerator 1 and denominator integer K>0.
    The complement (complementary unit fraction) is 1 - 1/K == (K - 1) / K.

1/K + (K - 1)/K == (1 + (K - 1)) / K == (K + 1 - 1) / K == K/K == 1
    [ "The Rational Number n/p  as a sum of two unit fractions"
      Konstantine Zelator, 2012-Feb-29. https://arxiv.org/pdf/1203.0018

0/K, 1/K, 2/K, 3/K, ... (K-2)/K, (K-1)/K, K/K
     ^ unit fraction              ^ complementary unit fraction
     ^ Qunit fraction             ^ Qcomplement

0/1 < Qunit < ... <  Qcomplement  < 1/1

subnormal_min(nFracBits(T)) == Qunit(nFracBits(T))
subnormal_max(nFracBits(T)) == Qcomplement(nFracBits(T))
