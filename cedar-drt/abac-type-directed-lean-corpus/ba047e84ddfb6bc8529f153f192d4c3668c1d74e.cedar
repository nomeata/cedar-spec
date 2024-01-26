permit(
  principal == a::"\0\0\0#\0\0\u{1}\u{11}\066\u{1}\u{1}\0#\0\0\u{1}\u{11}\06",
  action,
  resource is a in a::"\0\0\0#\0\0\u{1}\u{11}\066\u{1}\u{1}\0#\0\0\u{1}\u{11}\06"
) when {
  false
};
