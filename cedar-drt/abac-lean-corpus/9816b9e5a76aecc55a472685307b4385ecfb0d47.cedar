forbid(
  principal == a::"jjj\0\0\0\u{10}j",
  action in [Action::"action"],
  resource
) when {
  (true && (if (action * 32639) then false else resource)) && a::""
};
