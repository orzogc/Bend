# a literal lambda application is a beta-redex: check-app takes its beta
# steps, and the substituted body, a constructor, checks against the
# goal as any constructor does. in an infer position (a let's value) the
# step is infer-app's, and the constructor it leaves cannot infer.
import Base

law main:
  U32

def main(): (x => x)(3)

#|3
