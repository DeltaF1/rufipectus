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

// Comment test
class Square is Rectangle {
  construct new (width) {
       super(width, width)
  }
  foo { height }
}

var s = Square.new(10)
s.area()