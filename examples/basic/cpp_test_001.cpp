extern "C" {
  void echo(int x);
}

class Animal {
private:
  int age;
public:
  int get_age() {return age;};
  virtual void noise() {echo(0);};
  Animal(int a) {age=a;};
};

class Dog : public Animal {
public:
  void noise() {echo(1);};
  Dog(int a) : Animal(a) {};
};

class Cat : public Animal {
public:
  void noise() {echo(2);};
  Cat(int a) : Animal(a) {};
};

int main () {
  Dog fido = Dog(3);
  Cat mittens = Cat(4);
  fido.noise();
  echo(fido.get_age());
  mittens.noise();
  echo(mittens.get_age());
  return 0;
}
