@o("666665")
permit(
  principal,
  action,
  resource in a::"\0)\0\0\0\0\0\07\0\t"
) when {
  ((true && (!([ip("213.213.213.121")].containsAny([ip("d5d5:d5d5:d5d5:d5d5:d5d5:d5b:d523:2d5/84")])))) && ([[], [], []].containsAny([]))) && false
};
