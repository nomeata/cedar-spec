@A("6")
permit(
  principal == a::"\0\0\0\0\0\0\03",
  action,
  resource
) when {
  true
};
