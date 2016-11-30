
#include "stdio.h"

extern "C" {
  void echo(int x);
}

class Animal {
private:
  int age;
public:
  int get_age() {return age;};
  virtual void noise() =0;
  Animal(int a) {age=a;};
};

class Dog : public Animal {
public:
  Dog(int a) : Animal(a) {};
  virtual void noise() {echo(1);};
};

class Cat : public Animal {
public:
  Cat(int a) : Animal(a) {};
  virtual void noise() {echo(2);};
};

void make_noise(Animal* a) {
  a->noise();
  return;
}

int main () {
  Dog fido = Dog(3);
  Cat mittens = Cat(4);
  make_noise(&fido);
  make_noise(&mittens);
  return 0;
}
