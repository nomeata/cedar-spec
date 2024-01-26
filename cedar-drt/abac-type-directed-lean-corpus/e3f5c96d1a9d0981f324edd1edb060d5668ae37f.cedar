@A("\0")
permit(
  principal == a::"-rr",
  action,
  resource is a in a::"-rr"
) when {
  true && (!([[], []] == []))
};
