@r("&")
permit(
  principal is a in a::"",
  action,
  resource is a
) when {
  true && (((context == context) == (action == true)).containsAll(action))
};
