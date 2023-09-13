 class Rectangle {
   width { _width }
   height { _height }
   construct new (width, height) {
       _width = width
       _height = height
   }
   area() {
       return _width * _height
   }
 }

 class Square is Rectangle {
   construct new (width) {
        __classname = "Square"
        super(width, width)
   }

   hello {
        print("hello from%(__classname)")
   }

   foo { height }
 }

 var s = Square.new(10)
 s.hello
