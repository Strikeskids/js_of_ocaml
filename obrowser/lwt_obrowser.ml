
let sleep = Lwt_js.sleep
let yield = Lwt_js.yield
let run _ = Obj.magic ()

let js = JsString.of_string

external escape : string Js.t -> string Js.t = "escape"

let urlencode_string s =
  JsString.to_string (escape (js s))

let urlencode args =
  String.concat "&"
    (List.map
       (fun (n,v) -> urlencode_string n ^ "=" ^ urlencode_string v)
       args)

(*FIX: this is extremely slow;  *)
(* the following encode the whole string, even regular chars.
   Otherwise it does not work with Ocaml's Marshalled data *)
(*FIX: we probably want to simply escape the 8bit encoding of the string *)
let urlencode_string_ s =
  let hex c =
    Char.chr ((if c < 10 then Char.code '0' else Char.code 'A' - 10) + c)
  in
  let s' = String.make (String.length s * 3) ' ' in
  for i = 0 to String.length s - 1 do
    s'.[i * 3] <- '%' ;
    s'.[i * 3 + 1] <- hex ((Char.code s.[i]) lsr 4) ;
    s'.[i * 3 + 2] <- hex ((Char.code s.[i]) land 0xF)
  done ;
  s'

let urlencode_ args =
 String.concat "&"
   (List.map
      (fun (n,v) -> (urlencode_string_ n) ^ "=" ^ (urlencode_string_ v))
      args
   )

let http_get url args =
  let (res, w) = Lwt.wait () in
  let url = if args = [] then url else url ^ urlencode args in
  let req = Dom.XMLHttpRequest.create () in
  req##_open (js "GET", js url, Js._true, Js.null, Js.null);
  req##onreadystatechange <-
    (fun () ->
       if req##readyState = Dom.XMLHttpRequest.DONE then
         Lwt.wakeup w (req##status, JsString.to_string req##responseText));
  req##send (Js.null);
  res

let http_post url post_args =
  let (res, w) = Lwt.wait () in
  let req = Dom.XMLHttpRequest.create () in
  req##_open (js "POST", js url, Js._true, Js.null, Js.null);
  req##setRequestHeader
    (js"Content-type",js"application/x-www-form-urlencoded");
  req##onreadystatechange <-
    (fun () ->
       if req##readyState = Dom.XMLHttpRequest.DONE then
         Lwt.wakeup w (req##status, JsString.to_string req##responseText));
  req##send (Js.some (js (urlencode_ post_args)));
  res

let http_get_post url get_args post_args =
  let url = url ^ "?" ^ urlencode get_args in
  http_post url post_args