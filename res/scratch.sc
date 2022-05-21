import reflect.Selectable.reflectiveSelectable

def useInt(hasInt: {val n: Int; val b: Boolean}): Int = hasInt.n

def useInt2(hasInt: {val c: String; val b: Boolean; val n: Int}): Int = useInt(hasInt)

useInt(new Selectable{val b = true; val n = 10; val c = "hi"})

useInt2(new Selectable{val b = true; val n = 10; val c = "hi"})

def f(): String = { "".asInstanceOf[String] }